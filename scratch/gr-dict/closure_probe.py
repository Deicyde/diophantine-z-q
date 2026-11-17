import re, glob, collections
H = 'ZInQKernel/OneProof/H/'
START = re.compile(r'^(private )?(theorem|structure|def|noncomputable def|abbrev|lemma) ([A-Za-z_][\w\'.]*)')
STOP = re.compile(r'^(private |@\[|theorem|lemma|structure|def|noncomputable|abbrev|end |namespace |section |/-|open |set_option|variable|#|attribute|instance|export|universe)')
blocks = collections.defaultdict(list)
for fn in sorted(glob.glob(H + '*.lean')):
    L = open(fn).read().split('\n')
    ns = []
    i = 0
    while i < len(L):
        l = L[i]
        m0 = re.match(r'^namespace (\S+)', l)
        if m0: ns.append(m0.group(1))
        m1 = re.match(r'^end (\S+)', l)
        if m1 and ns and ns[-1] == m1.group(1): ns.pop()
        m = START.match(l)
        if m:
            j = i + 1
            while j < len(L) and not STOP.match(L[j]):
                j += 1
            blocks[m.group(3)].append((fn, i + 1, '.'.join(ns), '\n'.join(L[i:j]).rstrip()))
            i = j
        else:
            i += 1
SN = ['OpenResearchLeaves%d' % k for k in [2,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]] + ['ResearchLeaves3', 'ResearchLeaves', 'OpenResearchLeaves']
def sig(text):
    return re.split(r':=| where', text, 1)[0]
def mentions(text):
    return any(re.search(r'(?<![\w.])' + s + r'(?![\w\'])', text) for s in SN)
todo = ['sixContactMin_of_open35']
copied = []
while todo:
    n = todo.pop()
    if n in copied: continue
    copied.append(n)
    for (fn, ln, ns, text) in blocks[n][:1]:
        for ident in set(re.findall(r'(?<![\w.])[A-Za-z_][\w\']*(?![\w\'])', text)):
            if ident in blocks and ident not in copied and ident != n:
                b = blocks[ident][0][3]
                if b.split()[0] in ('theorem','def','lemma','noncomputable') and mentions(sig(b)):
                    todo.append(ident)
for n in copied:
    b = blocks[n]
    print(n, len(b), b[0][0].split('/')[-1], b[0][1], b[0][2], len(b[0][3].split('\n')))
