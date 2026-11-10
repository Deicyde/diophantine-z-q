import sys, ap_search as s
def adm(A, v):
    S = s.splus(A); offs = [max(S)-c for c in S]
    bad = [p for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71] if v % p and len({(o*v) % p for o in offs}) == p]
    return bad
for A in [-70,-69,-68,0,-200,1000]:
    print(A, len(s.splus(A)), "primes that must divide v:", adm(A, 1))
