"""Parity check: no deck-invariant rational curve over Q on X_{beta,theta} (beta generic).
Gamma ⊂ Y of class aF_s + bF_t - sum m_cd E_cd, m constant on the 6 Galois orbits of nodes
(O1={11,22},O2={12,21},O3={33,44},O4={34,43},O5={13,24,14,23},O6={31,42,41,32}).
Gamma.L_c = b - sum_d m_cd, Gamma.M_d = a - sum_c m_cd. A rational double cover needs exactly 2
odd branches, forming a Galois orbit, i.e. on {L1,L2}, {L3,L4}, {M1,M2} or {M3,M4}: parity of
Gamma.L / Gamma.M must be odd on exactly that pair and even elsewhere. Enumerate mod 2."""
import itertools
orb = {(1,1):0,(2,2):0,(1,2):1,(2,1):1,(3,3):2,(4,4):2,(3,4):3,(4,3):3}
for c in (1,2):
    for d in (3,4): orb[(c,d)] = 4; orb[(d,c)] = 5
found = []
for a, b, *xs in itertools.product(range(2), repeat=8):
    m = {k: xs[v] for k, v in orb.items()}
    L = [(b - sum(m[(c,d)] for d in range(1,5))) % 2 for c in range(1,5)]
    M = [(a - sum(m[(c,d)] for c in range(1,5))) % 2 for d in range(1,5)]
    pat = tuple(L + M)
    for odd in ([0,1], [2,3], [4,5], [6,7]):
        if all(pat[i] == (1 if i in odd else 0) for i in range(8)):
            found.append((a, b, xs, odd))
print('admissible parity patterns:', found)
