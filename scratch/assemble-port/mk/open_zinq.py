"""assemble-port: inside `namespace HDec`, `open ZInQ` opens only `HDec.ZInQ` (Lean resolves the innermost namespace).
In the root-namespace assembly it opened the one `ZInQ` holding both the kernel's and the file's names, so on every
`open` line the bare token `ZInQ` becomes `_root_.ZInQ ZInQ` (both). Usage: python3 -I mk/open_zinq.py parts/*.lean"""
import re, sys
for path in sys.argv[1:]:
    L = open(path).read().split('\n'); n = 0
    for i, l in enumerate(L):
        if re.match(r'^\s*open\s', l) and not re.search(r'\bZInQ\s*\(', l):
            new = re.sub(r'(?<=\s)ZInQ(?=\s|$)', '_root_.ZInQ ZInQ', l)
            if new != l: L[i] = new; n += 1
    if n:
        open(path, 'w').write('\n'.join(L)); print(path, n)
