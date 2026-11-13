"""Assemble TSHecke.lean from verbatim pieces + TSHeckeMain.lean.part (run from repo root)."""
import sys
def lines(path, a, b):  # 1-indexed inclusive
    with open(path) as f:
        L = f.read().split('\n')
    return '\n'.join(L[a-1:b]) + '\n'
G = 'scratch/prop-ts-glue/PropTSGlue.lean'
A = 'scratch/aut-o-finite/AutOFinite.lean'
S = 'scratch/infra-smooth-dim/SmoothStalk.lean'
C = 'scratch/curve-glue/CIproof.lean.part'
out = []
out.append('import Mathlib\n' + lines(G, 1, 2) + 'import ZInQKernel.HDecomp.Textbook.SkolemNoether\n')
out.append(lines(G, 3, 906))
out.append('''
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# The five Hecke Props, copied verbatim from `scratch/prop-ts-glue/PropTSGlue.lean`
(lines 3356-3442, Part C, with the two composition theorems; namespace `PropTSGlue` and its
`open` line kept)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace PropTSGlue

open Polynomial G0ModField PropTSRed
open scoped TensorProduct

''')
out.append(lines(G, 3356, 3442))
out.append('\nend PropTSGlue\n\nend\n')
out.append('''
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# Copy of `scratch/aut-o-finite/AutOFinite.lean` (lines 3-1037), verbatim except for the imports
and the trailing `#print axioms` lines; it proves `LeafQM.AV.Pin.Exact.autO_mod_inner_exact`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section AutOCopy
''')
out.append(lines(A, 3, 1037))
out.append('end\n\nend AutOCopy\n')
out.append('''
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# Copy of `scratch/infra-smooth-dim/SmoothStalk.lean` (lines 3-388), verbatim except for the
import line; it proves `InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section SmoothStalkCopy
''')
out.append(lines(S, 3, 388))
out.append('end InfraSmoothDim\n\nend SmoothStalkCopy\n')
out.append('''
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# Copy of `scratch/curve-glue/CIproof.lean.part` (all of it), with the statement
`ComponentIrreducible` copied verbatim from `scratch/curve-glue/CurveGlueAll.lean` (line 1251),
wrapped in namespace `CIcopy`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section CICopy

open CategoryTheory AlgebraicGeometry

namespace CIcopy

''')
out.append(lines('scratch/curve-glue/CurveGlueAll.lean', 1251, 1253))
out.append('\n')
with open(C) as f:
    out.append(f.read())
out.append('\nend CIcopy\n\nend CICopy\n')
gf = open('scratch/ts-hecke/GenericFibre.lean').read().split('\n')
assert gf[0] == 'import Mathlib'
gf = [l for l in gf[1:] if not l.startswith('#print')]
out.append('''
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# `scratch/ts-hecke/GenericFibre.lean` (task ts-hecke, Mathlib only), minus its import and
`#print` lines: `GFC.genericFibreCount`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section GFCopy
''')
out.append('\n'.join(gf))
out.append('\nend GFCopy\n')
rc = open('scratch/ts-hecke/RamCount.lean').read().split('\n')
assert rc[0] == 'import Mathlib'
rc = [l for l in rc[1:] if not l.startswith('#print')]
out.append('''
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# `scratch/ts-hecke/RamCount.lean` (task ts-hecke, Mathlib only), minus its import and `#print`
lines: `RamCount.ramCount` (`e(Q) · #{ψ} = [E : F]` for Galois extensions).
════════════════════════════════════════════════════════════════════════════════════════════ -/

section RamCountCopy
''')
out.append('\n'.join(rc))
out.append('\nend RamCountCopy\n')
un = open('scratch/ts-hecke/Units.lean').read().split('\n')
assert un[0].startswith('import ZInQKernel.HDecomp.QM.Structures')
un = [l for l in un[1:] if not l.startswith('#print')]
out.append('''
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# `scratch/ts-hecke/Units.lean` (task ts-hecke), minus its import and `#print` lines:
`TSHeckeUnits.exists_unit_congr` (`𝒪^× → (𝒪/3𝒪)^×` is onto).
════════════════════════════════════════════════════════════════════════════════════════════ -/

section UnitsCopy
''')
out.append('\n'.join(un))
out.append('\nend UnitsCopy\n')
with open('scratch/ts-hecke/TSHeckeMain.lean.part') as f:
    out.append(f.read())
with open('scratch/ts-hecke/TSHecke.lean', 'w') as f:
    f.write(''.join(out))
print('written')
