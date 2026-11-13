"""Split scratch/image-plane/ImagePlaneFinal.lean into ZInQKernel/Contrib/Mobius/*.lean.
Body lines are copied verbatim; only headers (imports, module docstrings) are new."""
import sys, pathlib
root = pathlib.Path(__file__).resolve().parents[2]
src = (root / 'scratch/image-plane/ImagePlaneFinal.lean').read_text().split('\n')
L = lambda a, b: '\n'.join(src[a-1:b])  # 1-indexed inclusive
P = 'ZInQKernel.Contrib.Mobius.'
HDR = """/-!
# mobius-contrib: {title}

Part of the Contrib port (task mobius-contrib, 2026-11-13) of image-plane's single file
`scratch/image-plane/ImagePlaneFinal.lean` (which is curve-glue's `MobiusFinal.lean` plus
image-plane's (IC), (AD) and C2K proofs). This module is lines {a}-{b} of that file, verbatim.
{extra}-/
"""
parts = [
 ('InfraDim', ['Mathlib'], 45, 496, 'dimension theory of smooth schemes (infra-smooth-dim copy)', '', False),
 ('Glue', ['Mathlib', 'ZInQKernel.HDecomp.QM.Pin', 'ZInQKernel.HDecomp.Textbook.SkolemNoether',
           'Mathlib.LinearAlgebra.Lagrange', 'Mathlib.RingTheory.Polynomial.Resultant.Basic',
           'Mathlib.RingTheory.Polynomial.GaussLemma', 'Mathlib.FieldTheory.Separable',
           'Mathlib.FieldTheory.IsAlgClosed.Basic'], 498, 1711,
  'mobius-glue (`MobiusGlue` from the curve facts and T5)',
  '\nThe file\'s opening `noncomputable section` (its line 498) is kept as this module\'s first\ncommand.\n', False),
 ('CurveFacts', [P+'InfraDim', P+'Glue'], 1713, 3895, 'curve-glue (curve facts, C2K/C3K reductions, (CI))', '', True),
 ('ImagePlane', [P+'CurveFacts'], 3897, 4681, 'image-plane ((IC), (AD), C2K, `MobiusGlue` from T5)', '', False),
]
for name, imps, a, b, title, extra, prefix_nc in parts:
    body = L(a, b)
    out = '\n'.join('import ' + i for i in imps) + '\n\n' + HDR.format(title=title, a=a, b=b, extra=extra) + '\n'
    if prefix_nc:
        pass
    out += body.rstrip('\n') + '\n'
    if name == 'ImagePlane':
        out += '\n#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_T5\n#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_t5\n#print axioms LeafQM.AV.Pin.imagePlaneCurveClosed\n'
    (root / 'ZInQKernel/Contrib/Mobius' / (name + '.lean')).write_text(out)
    print(name, a, b, b - a + 1)
