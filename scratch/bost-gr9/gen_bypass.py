"""bost-gr9: generate the weaker-leaf bypass of the Bost field (scratch only).

Reads scratch/bost-gr9/closure.tsv (from Closure.lean: the declarations reachable from
HDec.HSyn.sixContactMin_of_open67 whose type mentions a bundle carrying the Bost field, in dependency order, with
their declaration ranges) and copies each one VERBATIM into the sub-namespace HDec.HSyn.GR9 (HDec.HSyn.SGRFold.x ->
HDec.HSyn.GR9.SGRFold.x), with only these edits:
  * structures: the field types BostLowerBoundAn / BostLowerBoundPrinted / HeightSplit.BostLowerBound become
    GaudronRemondSec9LowerAn / GaudronRemondSec9LowerPrinted / HeightSplit.GRBostBound (GR14 §9's -(3/2) dim form);
    in the top bundle OpenResearchLeaves48 the field is renamed gaudronRemondSec9LowerAn (new doc comment);
  * the three conversions of the field are replaced by their GR §9 analogues (same argument shapes):
      R3Residual.bostLowerBoundPrinted_of_an          -> BostGR9.sec9Printed_of_an
      SemiAbDescend.bostLowerBound_of_printed_chevalley -> BostGR9.grBostBound_of_sec9Printed_chevalley
      HeightSplit.r21_of_leaves'                       -> BostGR9.r21_of_grBost'
  * in the conversion out of the top bundle, n.bostLowerBoundAn -> n.gaudronRemondSec9LowerAn.
Unqualified names resolve innermost-namespace first, so copies call copies; everything else is the original.
Each copy is wrapped in the namespace/open/set_option context active at its original position.

Usage (repository root): python3 scratch/bost-gr9/gen_bypass.py > scratch/bost-gr9/GR9Bypass.lean
"""
import re, sys

H = 'ZInQKernel/OneProof/H/'
rows = [l.rstrip('\n').split('\t') for l in open('scratch/bost-gr9/closure.tsv', encoding='utf-8') if l.strip()]

FIELD_TYPES = [
    ('_root_.ZInQ.R3Residual.BostLowerBoundAn', '_root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn'),
    ('_root_.ZInQ.HeightFix.BostLowerBoundPrinted', '_root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted'),
    ('_root_.ZInQ.HeightSplit.BostLowerBound', '_root_.ZInQ.HeightSplit.GRBostBound'),
]
CONVS = [
    ('_root_.ZInQ.R3Residual.bostLowerBoundPrinted_of_an ', '_root_.ZInQ.BostGR9.sec9Printed_of_an '),
    ('_root_.ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley ',
     '_root_.ZInQ.BostGR9.grBostBound_of_sec9Printed_chevalley '),
    ("_root_.ZInQ.HeightSplit.r21_of_leaves' ", "_root_.ZInQ.BostGR9.r21_of_grBost' "),
]
TOP = 'HDec.HSyn.OpenResearchLeaves48'
TOPCONV = 'HDec.HSyn.openResearchLeaves46_of_OpenResearchLeaves47_cf'
TOPDOC = ('  /-- bost-gr9, printed form: Gaudron-Remond, Polarisations et isogenies, Duke Math. J. 163 (2014), section 9, '
          'proof of Lemme 9.1, p. 2098 (read by the locator audit; cited by the manuscript at L894-895, step E4): '
          'h_F(A) >= -(3/2) dim A for every abelian variety over a number field, Faltings\' original normalization, '
          'over ZInQ.R3Residual.IsAnStableHeight (the object of gaudronRemondThm14An). Replaces bostLowerBoundAn '
          '(strictly stronger: -(g/2) log(2 pi^2)); consumed through BostGR9.sec9Printed_of_an, '
          'BostGR9.grBostBound_of_sec9Printed_chevalley and BostGR9.r21_of_grBost\' (R21). -/')

SGR_SIBLINGS = ['added12_of_open29_hf_pz']

cache = {}
def lines_of(mod):
    if mod not in cache:
        path = mod.replace('.', '/') + '.lean'
        cache[mod] = open(path, encoding='utf-8').read().split('\n')
    return cache[mod]

def context(lines, upto):
    """Scope stack before line `upto` (1-based): list of [kind, name, [open/set_option lines]]."""
    stack = [['root', '', []]]
    for l in lines[:upto - 1]:
        s = l.strip()
        m = re.match(r'^namespace (\S+)$', s)
        if m:
            stack.append(['namespace', m.group(1), []]); continue
        m = re.match(r'^(noncomputable )?section( (\S+))?$', s)
        if m:
            stack.append(['section', m.group(3) or '', []]); continue
        m = re.match(r'^end( (\S+))?$', s)
        if m:
            nm = m.group(2) or ''
            # `end A.B` closes namespace A.B (pushed as one entry)
            stack.pop(); continue
        if (s.startswith('open ') and not s.endswith(' in')) or s.startswith('set_option '):
            if l.startswith(' '):
                continue
            stack[-1][2].append(s)
    return stack

out = []
for name, mod, s, e, kind in rows:
    s, e = int(s), int(e)
    L = lines_of(mod)
    st = context(L, s)
    ns = [x[1] for x in st if x[0] == 'namespace']
    full = '.'.join(ns)
    assert full.startswith('HDec.HSyn'), (name, full)
    # check the attached `open ... in` lines right before the range
    pre = []
    k = s - 2
    while k >= 0 and L[k].strip().endswith(' in') and L[k].strip().startswith('open '):
        pre.insert(0, L[k]); k -= 1
    text = '\n'.join(pre + L[s - 1:e])
    if kind == 'structure':
        for a, b in FIELD_TYPES:
            text = re.sub(re.escape(a) + r'\b', b, text)
        if name == TOP:
            tl = text.split('\n')
            i = [j for j, x in enumerate(tl) if x.strip().startswith('bostLowerBoundAn :')]
            assert len(i) == 1, name
            j = i[0]
            d = j - 1
            assert tl[d].rstrip().endswith('-/'), name
            while not tl[d].lstrip().startswith('/--'):
                d -= 1
            tl[d:j + 1] = [TOPDOC, '  gaudronRemondSec9LowerAn : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn']
            text = '\n'.join(tl)
        assert 'BostLowerBound ' not in text and 'BostLowerBoundAn' not in text and 'BostLowerBoundPrinted' not in text, name
    else:
        for a, b in CONVS:
            text = text.replace(a, b)
        if name == TOPCONV:
            assert text.count('n.bostLowerBoundAn') == 1
            text = text.replace('n.bostLowerBoundAn', 'n.gaudronRemondSec9LowerAn')
        for a, _ in CONVS:
            assert a not in text, (name, a)
    # SGRFold siblings that are not copied are not on the resolution path from HSyn.GR9.SGRFold: qualify them
    if '.SGRFold.' in name:
        for x in SGR_SIBLINGS:
            text = re.sub(r'(?<![.\w])' + x + r'\b', '_root_.HDec.HSyn.SGRFold.' + x, text)
    # emit with context: each scope re-opened; HDec.HSyn -> HDec.HSyn.GR9
    blk = ['-- copied from %s:%d (%s)' % (mod.replace('.', '/') + '.lean', s, name)]
    closers = []
    seen_hsyn = False
    for kind_, nm, opens in st[1:]:
        if kind_ == 'namespace':
            parts = nm.split('.')
            newparts = []
            for p in parts:
                newparts.append(p)
                if p == 'HSyn' and not seen_hsyn:
                    newparts.append('GR9'); seen_hsyn = True
            blk.append('namespace ' + '.'.join(newparts))
            closers.insert(0, 'end ' + '.'.join(newparts))
        else:
            blk.append('section')
            closers.insert(0, 'end')
        blk += opens
    assert seen_hsyn, name
    blk.append(text)
    blk += closers
    out.append('\n'.join(blk))

hdr = '''import ZInQKernel.OneProof.H.TailZ74
import ZInQKernel.Contrib.OneProof.GaudronRemondSection9

/-! # bost-gr9 fold dry run: the Bost field replaced by Gaudron–Rémond §9 (weaker-leaf bypass)

`ZInQ.BostGR9.GaudronRemondSec9LowerAn` (`h_F ≥ -(3/2) dim`) is weaker than the field `bostLowerBoundAn` it replaces
(`h_F ≥ -(g/2) log(2π²)`), so the next generation cannot map to `OpenResearchLeaves48`. This file copies the %d
declarations of the live path that carry the field (Closure.lean: the research bundles `OpenResearchLeaves8EB`–`48`,
their conversions, the height-row consumer and the `sixContactMin_of_open*` chain) verbatim into `HDec.HSyn.GR9`, with
the field's type weakened at each generation and its three conversions replaced by the GR §9 analogues
(`gen_bypass.py`). Scratch only; generated. -/

set_option linter.style.longLine false

''' % len(rows)
ftr = '''

/-- **The top theorem with the GR §9 leaf in place of `bostLowerBoundAn`.** -/
theorem HDec.HSyn.sixContactMin_of_open67_gr9 (r : HDec.HSyn.GR9.OpenResearchLeaves48)
    (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves27) : ZInQ.SixContactMin :=
  HDec.HSyn.GR9.sixContactMin_of_open67 r t l

#print axioms HDec.HSyn.sixContactMin_of_open67_gr9
'''
ftr += r'''
/-! Field check (scratch): the copied top bundle has the original's fields minus `bostLowerBoundAn`, plus
`gaudronRemondSec9LowerAn`, each other field with the same type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o := `HDec.HSyn.OpenResearchLeaves48
  let n := `HDec.HSyn.GR9.OpenResearchLeaves48
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"original fields: {fo.size}, copy fields: {fn.size}"
  logInfo m!"only in original: {fo.filter (!fn.contains ·)}; only in copy: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"
'''
print(hdr + '\n\n'.join(out) + ftr, end='')
