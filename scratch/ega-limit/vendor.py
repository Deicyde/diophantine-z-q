"""Vendor the AxiomMath/Stacks declaration files needed for EGA IV 8.10.5 (xii).
Usage: python3 vendor.py <stacks-src-root> [--dry]
Copies the import closure of TOPS (minus modules already vendored in CloudW01Spread) into
ZInQKernel/Contrib/OneProof/EGAProperLimit/, remapping imports, and writes SOURCE_MANIFEST.json."""
import re, sys, os, json, hashlib
SR = sys.argv[1]; DRY = '--dry' in sys.argv
REV = 'c496df0d9beea9deaeabcea8492605f9a0a2313b'
VR = 'ZInQKernel/Contrib/CloudW01Spread'; VP = 'ZInQKernel.Contrib.CloudW01Spread.'
NR = 'ZInQKernel/Contrib/OneProof/EGAProperLimit'; NP = 'ZInQKernel.Contrib.OneProof.EGAProperLimit.'
TOPS = ['StacksFrontier.AlgebraicGeometry.ProperLimitStage.Basic',
        'StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaNoetherian0200',
        'StacksFrontier.AlgebraicGeometry.SegreProdIso.Main',
        'StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal']
# Renames that avoid clashes with declarations already in the project's `Main` environment
# (CloudW07JacobiansCurves vendors frenzymath/Jacobian-Challenge, which declares the same four names).
# (file or '*', identifier token, replacement); applied as whole-identifier replacements.
RENAMES = [
    ('*', 'ProjectiveSpace', 'StacksProjectiveSpace'),
    ('StacksFrontier/AlgebraicGeometry/LimitMorphismAt/Dominant.lean',
     'isSchemeTheoreticallyDominant_toImage', 'isSchemeTheoreticallyDominant_toImage_stacks'),
    ('StacksFrontier/RingTheory/HomogeneousLocalization/BaseAlgebra.lean',
     'val_algebraMap', 'val_algebraMap_stacks'),
    ('StacksFrontier/RingTheory/HomogeneousLocalization/BaseAlgebra.lean',
     'val_fromZeroRingHom', 'val_fromZeroRingHom_stacks'),
]
def apply_renames(rel, body):
    lines = body.split('\n')
    for f, tok, new in RENAMES:
        if f == '*' or f == rel:
            pat = re.compile(r"(?<![\w'])" + re.escape(tok) + r"(?![\w'!?])")
            lines = [l if IMP.match(l) else pat.sub(new, l) for l in lines]
    return '\n'.join(lines)
IMP = re.compile(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+)(\S+)(.*)$')
def path(root, m): return os.path.join(root, m.replace('.', '/') + '.lean')
seen = {}; stack = list(TOPS)
while stack:
    m = stack.pop()
    if m.startswith(VP): m = m[len(VP):]
    if m in seen: continue
    if os.path.exists(path(VR, m)): seen[m] = 'V'; src = path(VR, m)
    elif os.path.exists(path(SR, m)): seen[m] = 'S'; src = path(SR, m)
    else: continue
    for line in open(src):
        mm = IMP.match(line)
        if mm and (mm.group(2).startswith('Stacks') or mm.group(2).startswith(VP)): stack.append(mm.group(2))
def remap(m):
    if m.startswith('Stacks'):
        return (VP if seen.get(m) == 'V' else NP) + m
    return m
files = []
for m, k in sorted(seen.items()):
    if k != 'S': continue
    src = path(SR, m); dst = path(NR, m)
    raw = open(src, 'rb').read(); text = raw.decode()
    out = []
    for line in text.split('\n'):
        mm = IMP.match(line)
        if mm: line = mm.group(1) + remap(mm.group(2)) + mm.group(3)
        out.append(line)
    last = max(i for i, l in enumerate(out) if IMP.match(l))
    out.insert(last + 1, '\n-- Port: the upstream lakefile sets `maxSynthPendingDepth = 3` for every file.\nset_option maxSynthPendingDepth 3')
    rel = m.replace('.', '/') + '.lean'
    hdr = ('/-\nPorted from AxiomMath/Stacks, revision %s.\nSource: %s\n'
           'Upstream license: Apache-2.0; see EGAProperLimit/LICENSE.\n'
           'Modification notice (2026-11-16): import paths remapped into EGAProperLimit (modules already\n'
           'vendored in CloudW01Spread are imported from there); the upstream lakefile option\n'
           '`maxSynthPendingDepth = 3` is set in the file; four declaration names that clash with\n'
           'CloudW07JacobiansCurves are renamed (ProjectiveSpace -> StacksProjectiveSpace, and three\n'
           'lemmas get the suffix _stacks; see NOTICE.md). The mathematical content and proofs are unchanged.\n-/\n') % (REV, rel)
    body = apply_renames(rel, '\n'.join(out))
    files.append(dict(module=m, source_path=rel,
        source_url='https://raw.githubusercontent.com/AxiomMath/Stacks/%s/%s' % (REV, rel),
        source_sha256=hashlib.sha256(raw).hexdigest(), source_bytes=len(raw), destination=dst))
    if not DRY:
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w').write(hdr + body)
print(len(files), 'new files;', sum(1 for k in seen.values() if k == 'V'), 'reused from CloudW01Spread')
if not DRY:
    json.dump(dict(repository='https://github.com/AxiomMath/Stacks', revision=REV, license='Apache-2.0',
                   mathlib_revision='56a005855ea17e0b0958f73ec801ae140b0a1679',
                   lean_toolchain='leanprover/lean4:v4.35.0', tops=TOPS, files=files),
              open(os.path.join(NR, 'SOURCE_MANIFEST.json'), 'w'), indent=2)
