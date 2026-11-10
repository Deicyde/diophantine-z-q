"""Map identical line blocks between two TeX sources (ranges only, no text).
Usage: python3 -I linemap.py OLD a b NEW c d [minlen]
Prints blocks 'OLD x-y = NEW u-v (n lines)' of at least minlen identical lines
(whitespace-stripped comparison), and the NEW ranges not covered."""
import sys, difflib
o, a, b, n, c, d = sys.argv[1], *map(int, sys.argv[2:4]), sys.argv[4], *map(int, sys.argv[5:7])
minlen = int(sys.argv[7]) if len(sys.argv) > 7 else 3
O = open(o, encoding='utf-8').read().replace('\r', '').split('\n')[a-1:b]
N = open(n, encoding='utf-8').read().replace('\r', '').split('\n')[c-1:d]
sm = difflib.SequenceMatcher(None, [x.strip() for x in O], [x.strip() for x in N], autojunk=False)
cov = [False] * len(N)
tot = 0
for blk in sm.get_matching_blocks():
    if blk.size >= minlen:
        print(f"OLD {a+blk.a}-{a+blk.a+blk.size-1} = NEW {c+blk.b}-{c+blk.b+blk.size-1} ({blk.size} lines)")
        tot += blk.size
        for k in range(blk.b, blk.b + blk.size): cov[k] = True
print(f"# identical lines in blocks >= {minlen}: {tot} of {len(N)} new lines")
i = 0
while i < len(N):
    if not cov[i]:
        j = i
        while j < len(N) and not cov[j]: j += 1
        print(f"NEW-only {c+i}-{c+j-1} ({j-i} lines)")
        i = j
    else: i += 1
