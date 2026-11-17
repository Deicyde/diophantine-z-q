import sys
sys.path.insert(0, '.')
exec(open('eonly.py').read().split('L = int(sys.argv[1])')[0])
res = {}
for k in range(37, 52):
    for L in (7, 8, 9):
        s = search(12, k, L)
        if s:
            res[k] = (L, s[0]); break
    print(k, res.get(k), flush=True)
