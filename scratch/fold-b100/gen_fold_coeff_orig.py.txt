"""Generate TailZ63 (coeff-field-tc fold): the research chain 32..38 copied without the two coeff-rational leaves.

Each copied declaration is the original with exactly these edits:
  * bundle names OpenResearchLeaves{j} -> OpenResearchLeaves{j}CF (j = 32..37), OpenResearchLeaves38 -> OpenResearchLeaves39;
  * converter names renamed accordingly;
  * the fields gamma1IntegralSpan, heckePrimeIntegralToRational (and their doc comments) deleted from the structures;
  * their pass-through lines deleted from the converters;
  * `_root_.CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan n.heckePrimeIntegralToRational`
    replaced by `_root_.eigenformCoeffFieldFinite_proof`.
"""
import re, sys
H = sys.argv[1]
FIELDS = ('gamma1IntegralSpan', 'heckePrimeIntegralToRational')
OLD = '_root_.CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan n.heckePrimeIntegralToRational'
NEW = '_root_.eigenformCoeffFieldFinite_proof'
def bname(j):
    return 'OpenResearchLeaves39' if j == 38 else ('OpenResearchLeaves%dCF' % j if 32 <= j <= 37 else 'OpenResearchLeaves%d' % j)
def cname(j):
    return 'openResearchLeaves%d%s_of_%s' % (j - 1, 'CF' if j - 1 >= 32 else '', bname(j))
def ren(s):
    for j in range(38, 31, -1):
        s = re.sub(r'\bOpenResearchLeaves%d\b' % j, bname(j), s)
        s = re.sub(r'\bopenResearchLeaves%d_of_' % j, 'openResearchLeaves%dCF_of_' % j, s)
    return s
out = []
calls = {}
for k, j in enumerate(range(32, 39)):
    f = H + 'TailZ%d.lean' % (56 + k)
    s = open(f, encoding='utf-8').read()
    # structure block
    m = re.search(r'(/-- [^\n]*\n)?structure OpenResearchLeaves%d : Prop where\n(.*?)\n\n' % j, s, re.S)
    assert m, (f, 'structure')
    lines = m.group(2).split('\n')
    keep = []
    i = 0
    while i < len(lines):
        l = lines[i]
        if l.startswith('  /--'):
            # doc comment possibly multi-line, attached to next field
            doc = [l]
            while not doc[-1].rstrip().endswith('-/'):
                i += 1; doc.append(lines[i])
            i += 1
            fld = lines[i]
            if fld.strip().split(' ')[0] in FIELDS:
                i += 1; continue
            keep += doc + [fld]; i += 1; continue
        if l.strip().split(' ')[0] in FIELDS:
            i += 1; continue
        keep.append(l); i += 1
    doc = '/-- `%s` without `gamma1IntegralSpan` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/\n' % ('OpenResearchLeaves%d' % j)
    out.append(doc + 'structure %s : Prop where\n' % bname(j) + '\n'.join(keep) + '\n')
    # converter block
    m = re.search(r'(/-- [^\n]*\n)?(theorem openResearchLeaves%d_of_OpenResearchLeaves%d (.*?)\n)((?:  .*\n)+)' % (j - 1, j), s)
    assert m, (f, 'converter')
    head = m.group(2); body = m.group(4)
    assert body.count(OLD) <= 1
    body = body.replace(OLD, NEW)
    body = '\n'.join(l for l in body.split('\n') if l.strip().split(' ')[0] not in FIELDS) 
    assert 'gamma1IntegralSpan' not in body and 'heckePrimeIntegralToRational' not in body
    origname = 'openResearchLeaves%d_of_OpenResearchLeaves%d' % (j - 1, j)
    assert head.startswith('theorem ' + origname + ' ')
    head = 'theorem ' + cname(j) + ren(head[len('theorem ' + origname):])
    out.append('/-- `%s`, copied from `TailZ%d` with the coeff-field-tc edits. -/\n' % (head.split(' ')[1], 56 + k) + head + body.rstrip('\n') + '\n')
    # top theorem call pattern
    m = re.search(r'theorem sixContactMin_of_open(\d+) \(r : OpenResearchLeaves%d\) (.*?) : ZInQ\.SixContactMin :=\n  sixContactMin_of_open(\d+) \((\w+) r([^)]*)\) t l' % j, s)
    assert m, (f, 'top')
    calls[j] = (m.group(4), m.group(5).strip())
expr = 'r'
for j in range(38, 31, -1):
    conv, extra = calls[j]
    assert conv == 'openResearchLeaves%d_of_OpenResearchLeaves%d' % (j - 1, j), conv
    conv = cname(j)
    expr = '(%s %s%s)' % (conv, expr, (' ' + extra) if extra else '')
top = ('/-- **G0 with only the open leaves and the open glue** (coeff-field-tc): `sixContactMin_of_open55` without the leaves\n'
       '`gamma1IntegralSpan` and `heckePrimeIntegralToRational`, through the copied chain. -/\n'
       'theorem sixContactMin_of_open56 (r : OpenResearchLeaves39) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves25) : ZInQ.SixContactMin :=\n'
       '  sixContactMin_of_open48 %s t l\n' % expr)
hdr = '''import ZInQKernel.OneProof.H.TailZ62
import ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFiniteProof

/-! # OneProof H, coeff-field-tc: `sixContactMin_of_open56`

`eigenformCoeffFieldFinite` (the field of `OpenResearchLeaves31` that coeff-rational's fold, `TailZ56`, replaced by the
leaves `gamma1IntegralSpan` and `heckePrimeIntegralToRational`) is proved outright by
`eigenformCoeffFieldFinite_proof` (`ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFiniteProof.lean`, from Tau Ceti's
finiteness over `ℤ` of the cusp-form Hecke algebra; docs/research/coeff-field-tc.md). The two leaves are read only
where they give `eigenformCoeffFieldFinite` (`TailZ56`'s conversion and the `r17` line of `TailZ57`'s).

This module copies the research generations `OpenResearchLeaves32`–`38` and their conversions from `TailZ56`–`TailZ62`,
verbatim up to the renaming `OpenResearchLeaves<j> ↦ OpenResearchLeaves<j>CF` (`OpenResearchLeaves38 ↦
OpenResearchLeaves39`), with the two fields and their pass-through lines deleted and their one reading replaced by
`_root_.eigenformCoeffFieldFinite_proof`. The originals are unchanged. No new leaf. Generated by
`scratch/coeff-field-tc/gen_fold.py`. -/

set_option linter.style.longLine false

namespace HDec

namespace HSyn

'''
ftr = '''
end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open56
'''
print(hdr + '\n'.join(out) + '\n' + top + ftr, end='')
