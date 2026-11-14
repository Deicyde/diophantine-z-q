# For each duplicated name in dupscan output, print the statement (decl line up to ':=' / 'where')
# from both files, and whether they are textually identical (whitespace-normalised).
import re, sys, collections
pairs = collections.defaultdict(list); cur=None
for line in open(sys.argv[1]):
    if not line.startswith(' '): cur=line.strip()
    else: pairs[cur].append(line.strip())
def stmt(f, short):
    L = open(f).read().split('\n')
    for i,l in enumerate(L):
        if re.search(r'\b(theorem|lemma|def|abbrev|structure|class|inductive)\s+(_root_\.)?'+re.escape(short)+r'(\s|$)', l):
            s=[]
            for l2 in L[i:i+40]:
                s.append(l2)
                if ':=' in l2 or re.search(r'\bwhere\b', l2): break
            t=' '.join(s); t=re.split(r':=|\bwhere\b', t)[0]
            return ' '.join(t.split())
    return None
for n, fs in pairs.items():
    short=n.split('.')[-1]
    a,b=[stmt(f,short) for f in fs]
    print(('SAME ' if a==b else 'DIFF ')+n)
    if a!=b: print('   A:',a); print('   B:',b)
