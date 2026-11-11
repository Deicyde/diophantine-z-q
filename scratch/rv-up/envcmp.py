#!/usr/bin/env python3
"""envcmp.py A B label... : extract the environment carrying \\label{L} in A and B
(from its \\begin line to the matching \\end), strip CR, compare byte-for-byte.
Also: --range A a1 a2 B b1 b2 compares physical line ranges."""
import sys, re
def lines(f): return [l.rstrip('\r\n') for l in open(f, encoding='utf-8', newline='')]
def env(L, label):
    for i,l in enumerate(L):
        if '\\label{%s}'%label in l:
            m = re.search(r'\\begin\{(\w+\*?)\}', l)
            j = i
            if not m:
                j = i
                while j>=0 and not re.search(r'\\begin\{', L[j]): j -= 1
                m = re.search(r'\\begin\{(\w+\*?)\}', L[j])
            name = m.group(1); depth=0
            for k in range(j, len(L)):
                depth += L[k].count('\\begin{%s}'%name) - L[k].count('\\end{%s}'%name)
                if depth==0: return j+1, k+1, L[j:k+1]
    return None
if sys.argv[1]=='--range':
    A,a1,a2,B,b1,b2 = sys.argv[2:8]
    x = lines(A)[int(a1)-1:int(a2)]; y = lines(B)[int(b1)-1:int(b2)]
    print('IDENTICAL' if x==y else 'DIFFER', len(x), len(y)); sys.exit()
A,B = lines(sys.argv[1]), lines(sys.argv[2])
for lab in sys.argv[3:]:
    ea, eb = env(A,lab), env(B,lab)
    if not ea or not eb: print(lab, 'MISSING', bool(ea), bool(eb)); continue
    print(f"{lab}: A {ea[0]}-{ea[1]}  B {eb[0]}-{eb[1]}  ", 'IDENTICAL' if ea[2]==eb[2] else 'DIFFER')
