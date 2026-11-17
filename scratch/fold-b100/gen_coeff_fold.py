"""Generate the coeff-field-tc copy reroute on the current top (fold-b100, step 1).

`eigenformCoeffFieldFinite_proof` (ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFiniteProof.lean) proves
`DSCoeffExt.EigenformCoeffFieldFinite` outright. The research fields `heckePrimeIntegralToRational` and the gamma1 field
(`gamma1IntegralSpan` up to `OpenResearchLeaves43`, `gamma1IntegralBasis` from `OpenResearchLeaves44`, TailZ70) are
read only through `CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan n.heckePrimeIntegralToRational`
(and `gamma1IntegralSpan` from `gamma1IntegralBasis` in TailZ70's conversion).

The script walks the live path from the top theorem down: starting at the research bundle of the top theorem it follows
each conversion `<conv> (n : B_j) ... : B_{j-1}` while `B_{j-1}` still carries one of the fields, copying every bundle
and every conversion with exactly these edits:
  * bundle names B -> B + 'CF' (the top bundle OpenResearchLeaves<k> -> OpenResearchLeaves<k+1>), conversions -> name + '_cf';
  * the fields (and their doc comments) deleted from the structures, their pass-through lines deleted from the conversions;
  * the reading replaced by `_root_.eigenformCoeffFieldFinite_proof`.
The path and the call of each conversion are given in PATH below (verified against the sources by the asserts); the
last conversion lands in the first bundle without the fields (OpenResearchLeaves31EB), whose top theorem is BASE.

Usage (repository root):  python3 scratch/fold-b100/gen_coeff_fold.py > ZInQKernel/OneProof/H/TailZ<j>.lean
On a later head: add the new top generations to PATH (each new conversion of the research bundle; generations of the
textbook/added bundles enter through T17/OAL if they change), set TOPMOD / TOPTHM / NEWTOP, rerun, and edit Main.
"""
import re, sys, glob

H = 'ZInQKernel/OneProof/H/'
FIELDS = ('gamma1IntegralSpan', 'gamma1IntegralBasis', 'heckePrimeIntegralToRational')
OLD = '_root_.CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan n.heckePrimeIntegralToRational'
NEW = '_root_.eigenformCoeffFieldFinite_proof'

# (bundle, file, conversion to the next lower bundle, its extra args written with t16 / l)
PATH = [
    ('OpenResearchLeaves45', 'TailZ71', 'openResearchLeaves44_of_OpenResearchLeaves45', ''),
    ('OpenResearchLeaves44', 'TailZ70', 'openResearchLeaves43_of_OpenResearchLeaves44', ''),
    ('OpenResearchLeaves43', 'TailZ68', 'openResearchLeaves42_of_OpenResearchLeaves43', ''),
    ('OpenResearchLeaves42', 'TailZ67', 'openResearchLeaves41_of_OpenResearchLeaves42', ''),
    ('OpenResearchLeaves41', 'TailZ66', 'openResearchLeaves40_of_OpenResearchLeaves41', ''),
    ('OpenResearchLeaves40', 'TailZ65', 'openResearchLeaves39_of_OpenResearchLeaves40', ''),
    ('OpenResearchLeaves39', 'TailZ63', 'openResearchLeaves38EB_of_OpenResearchLeaves39', 't16'),
    ('OpenResearchLeaves38EB', 'EichlerBoundCopy', 'openResearchLeaves37_of_OpenResearchLeaves38_eb', 't16'),
    ('OpenResearchLeaves37EB', 'EichlerBoundCopy', 'openResearchLeaves36_of_OpenResearchLeaves37_eb', 't16'),
    ('OpenResearchLeaves36EB', 'EichlerBoundCopy', None, None),  # structure here; conversion below (TailZ69)
    ('OpenResearchLeaves35EB', 'EichlerBoundCopy', 'openResearchLeaves34_of_OpenResearchLeaves35_eb', 't16'),
    ('OpenResearchLeaves34EB', 'EichlerBoundCopy', 'openResearchLeaves33_of_OpenResearchLeaves34_eb', 't16'),
    ('OpenResearchLeaves33EB', 'EichlerBoundCopy', 'openResearchLeaves32_of_OpenResearchLeaves33_eb', ''),
    ('OpenResearchLeaves32EB', 'EichlerBoundCopy', 'openResearchLeaves31_of_OpenResearchLeaves32_eb', ''),
]
# the live conversion out of OpenResearchLeaves36EB is fold-kleiman2's copy in TailZ69 (takes OpenAddedLeaves26)
CONV36 = ('TailZ69', 'openResearchLeaves35_of_OpenResearchLeaves36_eb_k954', 't16 l')
BASE = 'sixContactMin_of_open48_eb_k954'   # (r : OpenResearchLeaves31EB) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves26)
TOPMOD = 'TailZ71'
TOPTHM = 'sixContactMin_of_open64'
NEWTOP = 'sixContactMin_of_open65'
NEWTOPBUNDLE = 'OpenResearchLeaves46'

def src(f):
    return open(H + f + '.lean', encoding='utf-8').read()

def bname(b):
    return NEWTOPBUNDLE if b == PATH[0][0] else b + 'CF'

def ren(s):
    for b, _, _, _ in PATH:
        s = re.sub(r'\b%s\b' % b, bname(b), s)
    return s

def block(s, head_re):
    """The declaration starting at a line matching head_re, through its indented lines."""
    m = re.search(r'^' + head_re + r'.*$', s, re.M)
    assert m, head_re
    lines = s[m.start():].split('\n')
    out = [lines[0]]
    for l in lines[1:]:
        if l.startswith('  ') or (l.startswith('    ') and out):
            out.append(l)
        else:
            break
    return out

def strip_struct(lines):
    keep, i = [], 0
    while i < len(lines):
        l = lines[i]
        if l.startswith('  /--'):
            doc = [l]
            while not doc[-1].rstrip().endswith('-/'):
                i += 1; doc.append(lines[i])
            i += 1
            fld = lines[i]
            if fld.strip().split(' ')[0] not in FIELDS:
                keep += doc + [fld]
            i += 1; continue
        if l.strip().split(' ')[0] not in FIELDS:
            keep.append(l)
        i += 1
    return keep

def strip_conv(lines):
    body = [l.replace(OLD, NEW) for l in lines]
    out = []
    i = 0
    while i < len(body):
        l = body[i]
        if l.startswith('  ') and not l.startswith('   ') and l.strip().split(' ')[0] in FIELDS:
            i += 1
            while i < len(body) and body[i].startswith('    '):
                i += 1
            continue
        out.append(l); i += 1
    return out

out = []
nread = 0
for k, (b, f, conv, args) in enumerate(PATH):
    s = src(f)
    st = block(s, r'structure %s : Prop where' % b)
    keep = strip_struct(st[1:])
    gone = len(st) - 1 - len(keep)
    pair = []
    pair.append('/-- `%s` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: '
               '`eigenformCoeffFieldFinite` is proved outright). -/\n' % b
               + 'structure %s : Prop where\n' % bname(b) + '\n'.join(keep) + '\n')
    if conv is None:
        f2, conv, args = CONV36
        s2 = src(f2)
    else:
        f2, s2 = f, s
    cv = block(s2, r'theorem %s \(n : %s\)' % (conv, b))
    nread += sum(l.count(OLD) for l in cv)
    head = cv[0]
    new = conv + '_cf'
    head = 'theorem ' + new + ren(head[len('theorem ' + conv):])
    body = strip_conv(cv[1:])
    txt = '\n'.join([head] + body)
    for fl in FIELDS:
        assert fl not in txt, (conv, fl)
        assert fl not in '\n'.join(keep), (b, fl)
    pair.append('/-- `%s`, copied from `%s` with the coeff-field-tc edits. -/\n' % (conv, f2) + txt + '\n')
    out[0:0] = pair
    PATH[k] = (b, f, conv, args)

assert nread == 4, nread   # TailZ65 (2: r11r12, eigenformHTNew), 33EB->32EB (r17), 32EB->31EB (eigenformCoeffFieldFinite)

expr = 'r'
for b, f, conv, args in PATH:
    a = (' ' + args) if args else ''
    expr = '(%s_cf %s%s)' % (conv, expr, a)
# check the top theorem's path: TOPTHM ... goes down to BASE through the same conversions (by the module chain read above)
assert re.search(r'theorem %s \(r : %s\) \(t : OpenTextbookLeaves17\) \(l : OpenAddedLeaves26\)' % (TOPTHM, PATH[0][0]), src(TOPMOD))
top = ('/-- **G0 with only the open leaves and the open glue** (coeff-field-tc, fold-b100): `%s` without the fields\n'
       '`gamma1IntegralBasis` and `heckePrimeIntegralToRational`, through the copied chain (`eigenformCoeffFieldFinite_proof`). -/\n'
       'theorem %s (r : %s) (t : OpenTextbookLeaves17) (l : OpenAddedLeaves26) : ZInQ.SixContactMin :=\n'
       '  let t16 := openTextbookLeaves16_of_OpenTextbookLeaves17 t\n'
       '  %s %s t16 l\n' % (TOPTHM, NEWTOP, NEWTOPBUNDLE, BASE, expr))
hdr = '''import ZInQKernel.OneProof.H.%s
import ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFiniteProof

/-! # OneProof H, coeff-field-tc (fold-b100): `%s`

`eigenformCoeffFieldFinite_proof` (`ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFiniteProof.lean`, from Tau Ceti's
finiteness over `ℤ` of the cusp-form Hecke algebra; docs/research/coeff-field-tc.md) proves
`DSCoeffExt.EigenformCoeffFieldFinite` outright. The research fields `heckePrimeIntegralToRational` and
`gamma1IntegralSpan` (from `OpenResearchLeaves44` on: `gamma1IntegralBasis`, gamma1-basis) are read only through
`CoeffRational.eigenformCoeffFieldFinite_of_heckePrime` (the conversions `32EB → 31EB`, `33EB → 32EB` of
`EichlerBoundCopy`, `40 → 39` of `TailZ65`) and, for `gamma1IntegralSpan`, from `gamma1IntegralBasis` (`TailZ70`).

This module copies the research generations on the live path, `OpenResearchLeaves32EB`–`38EB`, `39`–`45`, and their
conversions, verbatim up to the renaming `B ↦ BCF` (`OpenResearchLeaves45 ↦ OpenResearchLeaves46`, conversions with
suffix `_cf`), with the fields and their pass-through lines deleted and every reading replaced by
`_root_.eigenformCoeffFieldFinite_proof`. The originals are unchanged. No new leaf. Generated by
`scratch/fold-b100/gen_coeff_fold.py`. -/

set_option linter.style.longLine false

namespace HDec

namespace HSyn

''' % (TOPMOD, NEWTOP)
ftr = '''
end HSyn

end HDec

#print axioms HDec.HSyn.%s
''' % NEWTOP
print(hdr + '\n'.join(out) + '\n' + top + ftr, end='')
