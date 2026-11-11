"""For the analytic-rank-3 values of runs 1-2 (ranks taken from out_run*.txt, no new L-function runs):
g(n) and the alternative bracket readings. If the recursion's coefficient carried a factor 2 (e.g.
2^{h}L(d1)), Lemma N2 would give c_n(e) = 0 (e != n) and Prop N's analogue would say: rank>=2 => g(n) even.
Reading B of Theorem 1.2: T5a + g(n) + T5b even."""
import sys, re, glob
sys.path.insert(0, 'scratch/rv-prop-n')
from tyzlib import *
r3 = []
for f in sorted(glob.glob('scratch/rv-prop-n/out_run*.txt')):
    for line in open(f):
        m = re.match(r'(\d+) .*an_rank (\d+)', line)
        if m and int(m.group(2)) >= 3: r3.append(int(m.group(1)))
for n in r3:
    T5a, T5b = genus_sums(n)
    print(n, "g(n)", gCl(n), "T5a", T5a, "T5b", T5b, "readingB", (T5a + gCl(n) + T5b) % 2)
print(len(r3), "rank-3 values; with g(n)=1:", [n for n in r3 if gCl(n)])
