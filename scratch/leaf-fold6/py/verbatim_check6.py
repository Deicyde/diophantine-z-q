#!/usr/bin/env python3
"""leaf-fold6: verbatim checks of the 68 fields of `sixContactMin_of_open6`. Run from scratch/leaf-fold6 after
./assemble.sh (needs Leaves6.lean) and with olean/Check6 output in olean/Check6_out.txt (or _dev_out.txt).

A. Field type text. Every field line `name : type` of leaf-fold6's three new structures (part f20) has the same text
   as the same field of its source bundle: leaf-fold5's OpenTextbookLeaves5 / OpenAddedLeaves5 / OpenGlue5 (part e90)
   or leafq-check's OpenAddedLeaves10 (Fold.lean); `t8` is checked in C. OpenResearchLeaves5 is reused as is.
B. Provenance of the head constant of every field type (list from Check6's output). Chain constants (`HDec.…`): the
   declaration text in the flat file Leaves6.lean equals a declaration of the same name in some scratch source file
   outside the assemblies (leaf-fold*, h-decomposition, g0-assemble*); the files are listed. Kernel constants: the
   declaration is found in ZInQKernel/ (the field is the kernel's own constant, so its text is the kernel's).
C. T8: the kernel's `PoincareReducibility` (HDecomp/Objects.lean) has the text of pkg-I3's `I3.lean` and of the
   chain's copy (which leaf-fold4's T8 field used).
D. The leafq-check Props new in the bundles (STQM, ValenceFormulaGammaStar, QMHauptmodulBase3 and the definitions
   they use) have the same text in part f10, in leafq-check's Fold.lean and in leafq-check's standalone files.
"""
import os, re, sys, glob
sys.path.insert(0, 'py')
from chunks import chunks, text, fullnames

ROOT = '../..'
ok_all = True

def body(x):
    """the declaration without its leading docstring"""
    if x.startswith('/--'):
        return x[x.index('-/') + 2:].lstrip('\n')
    return x

def decls_by_short(t):
    d = {}
    for c in chunks(t):
        if c['kind'] == 'decl' and c['name']:
            d.setdefault(c['name'].split('.')[-1], []).append(text(c))
    return d

def struct_fields(t, sname):
    L = t.split('\n')
    i = next(k for k, l in enumerate(L) if l.startswith('structure %s ' % sname))
    out = {}; k = i + 1; indoc = False
    while k < len(L) and (L[k].startswith(' ') or L[k] == ''):
        l = L[k]
        if l.strip().startswith('/--'):
            indoc = '-/' not in l
        elif indoc:
            if '-/' in l: indoc = False
        elif l.startswith('  ') and not l.startswith('   ') and ' : ' in l:
            nm, ty = l.strip().split(' : ', 1)
            out[nm] = ty
        elif l.startswith('    ') and out:
            last = list(out)[-1]; out[last] += ' ' + l.strip()
        k += 1
    return out

print('== A. field type text')
f20 = open('parts/f20_fold6.lean').read()
e90 = open('../leaf-fold5/parts/e90_fold5.lean').read()
fold = open('../leafq-check/Fold.lean').read()
src = {'OpenTextbookLeaves6': [('e90 OpenTextbookLeaves5', struct_fields(e90, 'OpenTextbookLeaves5'))],
       'OpenAddedLeaves6': [('e90 OpenAddedLeaves5', struct_fields(e90, 'OpenAddedLeaves5')),
                            ('Fold OpenAddedLeaves10', struct_fields(fold, 'OpenAddedLeaves10'))],
       'OpenGlue6': [('e90 OpenGlue5', struct_fields(e90, 'OpenGlue5'))]}
nA = 0
for s, srcs in src.items():
    F = struct_fields(f20, s)
    print(' ', s, len(F), 'fields')
    for nm, ty in F.items():
        hit = [lab for lab, S in srcs if S.get(nm) == ty]
        if nm == 't8':
            print('    t8 : %s  (checked in C)' % ty); continue
        nA += 1
        if hit: print('    %s IDENTICAL to %s' % (nm, hit[0]))
        else: ok_all = False; print('    %s DIFFERENT: %s' % (nm, ty))
print('  fields checked:', nA)

print('== B. provenance of the head constants')
chk = 'olean/Check6_out.txt' if os.path.exists('olean/Check6_out.txt') else 'olean/Check6_dev_out.txt'
heads = []
for l in open(chk):
    m = re.match(r'  (\w+) : \(some ([\w.\']+)\)', l)
    if m: heads.append((m.group(1), m.group(2)))
assert len(heads) == 68, len(heads)
flat = open('Leaves6.lean').read()
FL = {}
for full, c in fullnames(chunks(flat)):
    if isinstance(full, str): FL.setdefault(full, []).append(text(c))
# source files outside the assemblies
ASSEMBLY = re.compile(r'\.\./(leaf-fold\d|h-decomposition|g0-assemble\d*)/|/olean/|Flat|/Leaves\d*\.lean$')
srcfiles = [f for f in glob.glob('../**/*.lean', recursive=True) + glob.glob('../**/*.lean.part', recursive=True)
            if not ASSEMBLY.search(f)] + ['../h-decomposition/Leaves.lean', '../av-b2/olean/AVB2Main.lean']
# (av-b2 keeps its own source AVB2Main.lean in its olean/ directory; h-decomposition/Leaves.lean is the synthesis)
SRC = {}; SRCB = {}
for f in srcfiles:
    try: t = open(f).read()
    except Exception: continue
    for short, txts in decls_by_short(t).items():
        for x in txts:
            SRC.setdefault((short, x), set()).add(f[3:])
            SRCB.setdefault((short, body(x)), set()).add(f[3:])
KER = {}
for f in glob.glob(ROOT + '/ZInQKernel/**/*.lean', recursive=True):
    for full, c in fullnames(chunks(open(f).read())):
        if isinstance(full, str): KER.setdefault(full, []).append(f[len(ROOT) + 1:])
nchain = nker = 0
for fld, h in heads:
    if h.startswith('HDec.'):
        nchain += 1
        # the chain declaration: Leaves6 names inside `namespace HDec`
        txts = FL.get(h, [])
        if len(txts) != 1:
            ok_all = False; print('  %s : %s  NOT FOUND ONCE in Leaves6 (%d)' % (fld, h, len(txts))); continue
        short = h.split('.')[-1]
        files = sorted(SRC.get((short, txts[0]), set()))
        filesb = sorted(SRCB.get((short, body(txts[0])), set()))
        more = lambda fs: ', '.join(fs[:3]) + (' (+%d)' % (len(fs) - 3) if len(fs) > 3 else '')
        if files:
            print('  %s : %s  IDENTICAL in %s' % (fld, h, more(files)))
        elif filesb:
            print('  %s : %s  IDENTICAL statement (docstring updated since) in %s' % (fld, h, more(filesb)))
        else:
            ok_all = False; print('  %s : %s  NO IDENTICAL SOURCE outside the assemblies' % (fld, h))
    else:
        nker += 1
        fs = KER.get(h, [])
        print('  %s : %s  kernel: %s' % (fld, h, ', '.join(fs) if fs else 'NOT FOUND'))
        if not fs: ok_all = False
print('  chain constants %d, kernel constants %d' % (nchain, nker))

print('== C. T8')
ker = [text(c) for full, c in fullnames(chunks(open(ROOT + '/ZInQKernel/HDecomp/Objects.lean').read()))
       if full == 'PkgI3.PoincareReducibility']
i3 = decls_by_short(open('../pkg-I3/I3.lean').read()).get('PoincareReducibility', [])
ch = FL.get('HDec.PkgI3.PoincareReducibility', [])
same = len(ker) == 1 and len(i3) == 1 and len(ch) == 1 and ker[0] == i3[0] and body(ch[0]) == body(ker[0])
print('  kernel PkgI3.PoincareReducibility = pkg-I3 I3.lean (with docstring):', ker == i3)
print('  kernel = chain HDec.PkgI3.PoincareReducibility (statement; the chain docstring has rv-leaves-b repair 2):',
      'IDENTICAL' if same else 'DIFFERENT')
ok_all &= bool(same)

print('== D. leafq-check Props')
f10 = open('parts/f10_leafq.lean').read()
D10 = decls_by_short(f10); DF = decls_by_short(fold)
stand = {'STQM': 'CMDescendsGlue.lean', 'TorsionDescends': 'CMDescendsGlue.lean', 'bcC': 'CMDescendsGlue.lean',
         'ValenceFormulaGammaStar': 'ValenceBound.lean', 'ellOrder': 'ValenceBound.lean',
         'EllipticOrderLe6': 'ValenceBound.lean',
         'QMHauptmodulBase3': 'QMHauptmodulCM.lean', 'QMHauptmodulBase2': 'QMHauptmodulCM.lean',
         'QMHauptmodulBase': 'QMHauptmodulCM.lean', 'x3': 'QMHauptmodulCM.lean'}
for n, f in stand.items():
    S = decls_by_short(open('../leafq-check/' + f).read()).get(n, [])
    a = D10.get(n, []); b = DF.get(n, [])
    same = len(a) == 1 and a == b and a[0] in S
    print('  %s: f10 = Fold.lean = %s: %s' % (n, f, 'IDENTICAL' if same else 'DIFFERENT (%d/%d/%d)' % (len(a), len(b), len(S))))
    ok_all &= same
print('ALL OK' if ok_all else 'MISMATCH')
