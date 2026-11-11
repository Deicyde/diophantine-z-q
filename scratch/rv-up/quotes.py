"""quotes.py CORPUS_LIST N5 FILE... : find spans of FILEs that reproduce upstream text.
Tokens = whitespace-split, lowercased, outer punctuation/backticks/markdown stripped. A word of FILE is 'covered' if it lies
in an 8-token shingle that occurs in some corpus file. Maximal covered runs of >= MINW words are printed with the corpus
file of their first shingle and whether the run also occurs in N5 (the fork's own copy of the 11/5 text)."""
import sys, re
K, MINW = 8, 25
def toks(s):
    out = []
    for w in s.split():
        w = w.strip('`*_|,.;:()[]"\'').lower()
        if w: out.append(w)
    return out
corpus = [l.rstrip('\n') for l in open(sys.argv[1])]
n5 = toks(open(sys.argv[2], encoding='utf-8', errors='replace').read())
files = sys.argv[3:]
F = {f: toks(open(f, encoding='utf-8', errors='replace').read()) for f in files}
want = {}
for f, t in F.items():
    for i in range(len(t) - K + 1):
        want.setdefault(tuple(t[i:i+K]), None)
for path in corpus:
    try:
        t = toks(open(path, encoding='utf-8', errors='replace').read())
    except Exception:
        continue
    for i in range(len(t) - K + 1):
        g = tuple(t[i:i+K])
        if g in want and want[g] is None:
            want[g] = path
n5set = set(tuple(n5[i:i+K]) for i in range(len(n5) - K + 1))
for f, t in F.items():
    cov = [False]*len(t); src = [None]*len(t)
    for i in range(len(t) - K + 1):
        g = tuple(t[i:i+K])
        if want.get(g):
            for k in range(i, i+K):
                cov[k] = True
                src[k] = src[k] or want[g]
    i = 0
    while i < len(t):
        if cov[i]:
            j = i
            while j < len(t) and cov[j]: j += 1
            if j - i >= MINW:
                inn5 = all(tuple(t[k:k+K]) in n5set for k in range(i, j - K + 1))
                print(f"{f}: {j-i} words, src {src[i].replace('/home/jackmccarthy/','~/')}, in N5: {inn5}\n    {' '.join(t[i:min(j, i+40)])}{' ...' if j-i > 40 else ''}")
            i = j
        else:
            i += 1
