"""Step 1 of the r16-shimura73 fold: put `r16CoreY` back on the top research bundle in place of the four
Diamond-Shurman fields that are read only to fill it.

On leaf-fold33b (TailZ74, top `sixContactMin_of_open67`), `r16CoreY` is filled in the conversion
`openResearchLeaves40_of_OpenResearchLeaves41_cf` by
`_root_.AfTateLam.r16CoreY_of_ds965 n.heckeJ1DS n.afShimura n.afCharpolyDS965 n.igusaGL2DS mumfordTorsionAlgClosed_proof`,
and the top fields heckeJ1DS, afShimura, afCharpolyDS965, igusaGL2DSGalSome (igusaGL2DS below the top) are read nowhere
else. This script copies the research generations OpenResearchLeaves48, 46CF, ..., 41CF of TailZ74 and their
conversions verbatim with exactly these edits:
  * names B -> B + 'R16' (the top OpenResearchLeaves48 -> OpenResearchLeaves49), conversions -> name + '_r16';
  * the four fields (with doc comments) deleted from the structures, the field `r16CoreY` added (doc copied from
    OpenResearchLeaves32EBCF);
  * in the conversions their pass-through lines deleted, `r16CoreY := n.r16CoreY` added, and the reading in
    41CF -> 40CF replaced by `n.r16CoreY`;
and writes the top theorem `sixContactMin_of_open68` (same body as open67 with the copied conversions).
`r16CoreY` is a consequence of the four fields (r16CoreY_of_ds965), so this is a weakening of the hypotheses.
Then `autofold.json` (step 2) discharges `r16CoreY` from the new leaves.

Usage (repository root): python3 scratch/r16-shimura73/gen_r16_restore.py > ZInQKernel/OneProof/H/TailZ75.lean
"""
import re

H = 'ZInQKernel/OneProof/H/'
SRC = 'TailZ74'
FIELDS = ('heckeJ1DS', 'afShimura', 'afCharpolyDS965', 'igusaGL2DS', 'igusaGL2DSGalSome')
OLD = ('_root_.AfTateLam.r16CoreY_of_ds965 n.heckeJ1DS n.afShimura n.afCharpolyDS965 n.igusaGL2DS '
       '_root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof')
PATH = [  # (bundle, conversion out of it)
    ('OpenResearchLeaves48', 'openResearchLeaves46_of_OpenResearchLeaves47_cf'),
    ('OpenResearchLeaves46CF', 'openResearchLeaves45_of_OpenResearchLeaves46_cf'),
    ('OpenResearchLeaves45CF', 'openResearchLeaves44_of_OpenResearchLeaves45_cf'),
    ('OpenResearchLeaves44CF', 'openResearchLeaves43_of_OpenResearchLeaves44_cf'),
    ('OpenResearchLeaves43CF', 'openResearchLeaves42_of_OpenResearchLeaves43_cf'),
    ('OpenResearchLeaves42CF', 'openResearchLeaves41_of_OpenResearchLeaves42_cf'),
    ('OpenResearchLeaves41CF', 'openResearchLeaves40_of_OpenResearchLeaves41_cf'),
]
TOPTHM, NEWTOP, NEWTOPBUNDLE = 'sixContactMin_of_open67', 'sixContactMin_of_open68', 'OpenResearchLeaves49'

s = open(H + SRC + '.lean', encoding='utf-8').read()

def bname(b):
    return NEWTOPBUNDLE if b == PATH[0][0] else b + 'R16'

def ren(t):
    for b, c in PATH:
        t = re.sub(r'\b%s\b' % b, bname(b), t)
        t = re.sub(r'\b%s\b' % c, c + '_r16', t)
    return t

def block(head_re):
    m = re.search(r'^' + head_re + r'.*$', s, re.M)
    assert m, head_re
    lines = s[m.start():].split('\n')
    out = [lines[0]]
    for l in lines[1:]:
        if l.startswith('  '):
            out.append(l)
        else:
            break
    return out

# the doc of r16CoreY
m = re.search(r'^(  /-- r16-split: R16_EichlerShimuraJ1\' with its rank-two clause deleted.*-/)\n  r16CoreY : _root_\.R16Split\.R16CoreY$', s, re.M)
assert m
R16DOC = m.group(1)
R16FIELD = '  r16CoreY : _root_.R16Split.R16CoreY'

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
    assert not any(l.strip().startswith('r16CoreY ') for l in keep)
    return keep + [R16DOC, R16FIELD]

def strip_conv(lines, last):
    out, i, nread = [], 0, 0
    while i < len(lines):
        l = lines[i]
        if l.startswith('  ') and not l.startswith('   ') and l.strip().split(' ')[0] in FIELDS:
            i += 1
            while i < len(lines) and lines[i].startswith('    '):
                i += 1
            continue
        if OLD in l:
            nread += 1
            l = l.replace(OLD, 'n.r16CoreY')
        out.append(l); i += 1
    if last:
        assert nread == 1
    else:
        assert nread == 0
        out.append('  r16CoreY := n.r16CoreY')
    return out

out = []
for k, (b, conv) in enumerate(PATH):
    st = block(r'structure %s : Prop where' % b)
    keep = strip_struct(st[1:])
    cv = block(r'theorem %s \(n : %s\)' % (conv, b))
    head = ren(cv[0])
    body = strip_conv(cv[1:], k == len(PATH) - 1)
    txt = '\n'.join([head] + [ren(l) for l in body])
    for fl in FIELDS:
        assert not re.search(r'\b%s\b' % fl, txt), (conv, fl)
        assert not re.search(r'\b%s\b' % fl, '\n'.join(keep[:-2])), (b, fl)
    pair = ['/-- `%s` with `r16CoreY` in place of heckeJ1DS, afShimura, afCharpolyDS965, igusaGL2DS(GalSome) '
            '(r16-shimura73, step 1; `r16CoreY` is their consequence `AfTateLam.r16CoreY_of_ds965`). -/\n' % b
            + 'structure %s : Prop where\n' % bname(b) + '\n'.join(keep) + '\n',
            '/-- `%s`, copied from `%s` with the r16-shimura73 edits. -/\n' % (conv, SRC) + txt + '\n']
    out[0:0] = pair

topb = block(r'theorem %s ' % TOPTHM)
top = '\n'.join(topb).replace('theorem ' + TOPTHM, 'theorem ' + NEWTOP)
top = ren(top)
assert '(r : %s)' % NEWTOPBUNDLE in top and top.count('_r16') == len(PATH)

hdr = '''import ZInQKernel.OneProof.H.%s

/-! # OneProof H, r16-shimura73 step 1: `%s` (`r16CoreY` back on the top research bundle)

On leaf-fold33b the research field `r16CoreY` (`R16Split.R16CoreY`) is filled in
`openResearchLeaves40_of_OpenResearchLeaves41_cf` from the four Diamond-Shurman fields heckeJ1DS, afShimura,
afCharpolyDS965, igusaGL2DS (igusaGL2DSGalSome on the top bundle) through `AfTateLam.r16CoreY_of_ds965`; they are read
nowhere else. This module copies the research generations `OpenResearchLeaves41CF`-`46CF` and `48` of `TailZ74` and
their conversions verbatim up to the renaming `B ↦ BR16` (`OpenResearchLeaves48 ↦ OpenResearchLeaves49`, conversions
with suffix `_r16`), with the four fields replaced by `r16CoreY` (a consequence of them), so that the next fold
(`scratch/r16-shimura73/autofold.json`) can discharge `r16CoreY` from the manuscript's own sources (Li 1975, Shimura
1973 Thm 1). The originals are unchanged. Generated by `scratch/r16-shimura73/gen_r16_restore.py`. -/

set_option linter.style.longLine false

namespace HDec

namespace HSyn

''' % (SRC, NEWTOP)
ftr = '''
end HSyn

end HDec

#print axioms HDec.HSyn.%s
''' % NEWTOP
print(hdr + '\n'.join(out) + '\n/-- **G0 with only the open leaves and the open glue** (r16-shimura73 step 1): `%s` with `r16CoreY` '
      'in place of the four Diamond-Shurman fields. -/\n' % TOPTHM + top + '\n' + ftr, end='')
