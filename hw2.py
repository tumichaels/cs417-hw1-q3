import prover as p
import compiler as c
import verifier as v
from utils import f_inner
import math

setup = c.Setup.from_file('powersOfTau28_hez_final_11.ptau')

def gen_input_assigments(i_in, ct_in, p_in,  s_in):
    assignments = {}
    public = []
    for i in range(len(ct_in)):
        for j in range(len(s_in)):
            assignments[f'a{i}{j}'] = ct_in[i][0][j]
            public.append(ct_in[i][0][j])
        assignments[f'b{i}'] = ct_in[i][1]
        public.append(ct_in[i][1])
    
    for i in range(len(s_in)):
        assignments[f's{i}'] = s_in[i]
    assignments['i'] = i_in
    public.append(i_in)
    assignments['p'] = p_in
    public.append(p_in)
    return assignments, public

def gen_public_input_eqs(n, s_len):
    eqs = []
    for i in range(n):
        for j in range(s_len):
            eqs.append(f'a{i}{j}pub public')
            eqs.append(f'a{i}{j}pub <== a{i}{j}')
        eqs.append(f'b{i}pub public')
        eqs.append(f'b{i}pub <== b{i}')
    eqs.append('ipub public')
    eqs.append('ipub <== i')
    eqs.append('ppub public')
    eqs.append('ppub <== p')
    eqs.sort(key=lambda x: "public" not in x)
    return eqs

def gen_encrypt(a, s_len):
    eqs = []
    for i in range(s_len):
        eqs.append(f'a{a}mul{i} <== s{i} * a{a}{i}')
    
    eqs.append(f'a{a}add1 <== a{a}mul0 + a{a}mul1')
    for i in range(2, s_len):
        eqs.append(f'a{a}add{i} <== a{a}add{i-1} + a{a}mul{i}')
    
    eqs.append(f'claimedB{a} <== a{a}add{s_len-1} + p')

    return eqs

def create_index_selector(n, i_val):
    eqs = []
    for i in range(n):
        eqs.append(f'sel{i}first <== {i} - i')
        diff = i - i_val
        inv = f_inner(1) / diff if diff != 0 else 0
        eqs.append(f'inv{i} <== {inv}')
        eqs.append(f'sel{i}second <== sel{i}first * inv{i}')
        eqs.append(f'sel{i} <== sel{i}second * -1 + 1')
    return eqs

def create_selector_mask_and_select(n, x):
    eqs = []
    for i in range(n):
        eqs.append(f'sel{x}{i}mask <== sel{i} * {x}{i}')
    eqs.append(f'selSum{x}1 <== sel{x}0mask + sel{x}1mask')
    for i in range(2, n):
        eqs.append(f'selSum{x}{i} <== selSum{x}{i-1} + sel{x}{i}mask')
    eqs.append(f'sel{x} <== selSum{x}{n-1}')
    return eqs

def check_i_in_range(n, i_in):
    eqs = []
    bit_len = int(math.log(n, 2))
    i_in_bits = [int(b) for b in bin(i_in)[2:].zfill(bit_len)]
    i_in_bits.reverse()
    for i in range(bit_len):
        pow2 = 2**i
        eqs.append(f'pow2{i} <== {pow2}')
        eqs.append(f'ibit{i} <== {i_in_bits[i]}')
        eqs.append(f'ibit{i} === ibit{i} * ibit{i}')
        eqs.append(f'imask{i} <== pow2{i} * ibit{i}')
    
    eqs.append('isum1 <== imask0 + imask1')
    for i in range(2, bit_len):
        eqs.append(f'isum{i} <== isum{i-1} + imask{i}')
    
    eqs.append(f'i === isum{bit_len-1}')
    return eqs

def circuit(n, s_len, i_in):
    eqs = []
    eqs.extend(gen_public_input_eqs(n, s_len))
    eqs.extend(check_i_in_range(n, i_in))
    for i in range(n):
        eqs.extend(gen_encrypt(i, s_len))
    eqs.extend(create_index_selector(n, i_in))
    eqs.extend(create_selector_mask_and_select(n, 'claimedB'))
    eqs.extend(create_selector_mask_and_select(n, 'b'))
    eqs.append('selclaimedB === selb')
    return eqs

S_LEN = 3
N = 8

ct_in = [
    ((3, 7, 11), 5),
    ((8, 2, 5), 19),
    ((5, 7, 2), 11),
    ((3, 1, 1), 8),
    ((2, 0, 10), 10),
    ((6, 12, 3), 5),
    ((5, 9, 3), 11),
    ((1, 0, 7), 5)
]
p_in = 6
s_in = (1, 0, 1)
i_in = 1
eqs = circuit(N, S_LEN, i_in)
vk = c.make_verification_key(setup, 256, eqs)
print("Generated verification key")
input_assignments, public = gen_input_assigments(i_in, ct_in, p_in, s_in)
assignments = c.fill_variable_assignments(eqs, input_assignments)
proof = p.prove_from_witness(setup, 256, eqs, assignments)
print("Generated proof")
assert v.verify_proof(setup, 256, vk, proof, public, optimized=True)
print("Verified proof")
