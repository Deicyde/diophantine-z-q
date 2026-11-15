"""Generate the contribution files under ZInQKernel/Contrib/OneProof/ from the compiled scratch files.

P1Scheme.lean            -> QuotientP1/P1Scheme.lean      (verbatim, minus #print)
Port1.lean L4..SPLIT-1   -> QuotientP1/MCRQuotA.lean      (Port1 = mcr-glue parts 5-6 + mcr-quot parts 1-24,
Port1.lean SPLIT..end    -> QuotientP1/MCRQuotB.lean       over TailW, namespace HDec)
final section            -> QuotientP1Coordinate.lean
Run from the worktree root: python3 -I scratch/p1-quot/py/gen_contrib.py
"""
import sys
ROOT = '.'
S = ROOT + '/scratch/p1-quot/'
D = ROOT + '/ZInQKernel/Contrib/OneProof/'
port = open(S + 'Port1.lean').read().split('\n')
assert port[0] == 'import ZInQKernel.OneProof.H.TailW'
header_lines = port[3:12]   # blank, namespace HDec, set_option, attribute (3 lines), blank
assert port[4] == 'namespace HDec', port[4]
split = next(i for i, l in enumerate(port) if l.startswith('# mcr-quot, part 12')) - 1
assert port[split].startswith('/-! ═')
CW = 'import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.'
partA = port[12:split]
partB = port[split:]

docA = '''/-!
# p1-quot, helper A: mcr-glue parts 5-6 and mcr-quot parts 1-11 over the chain

`scratch/mcr-quot/MCRQuot.lean` from its line 4406 on (mcr-glue parts 5-6, mcr-quot parts 1-24; everything before
that line is `scratch/mcr-glue/MCRGlue.lean`, which the chain holds as `TailL`..`TailW` in `namespace HDec`), verbatim
inside `namespace HDec`, except that `ImagePlane.*`, `curveFacts`, `smoothStalkDimOne` and one `transportLevel` are
written with the prefix `_root_.LeafQM.AV.Pin.` (inside `namespace HDec` the unqualified names resolve to the chain's
aliases or are ambiguous). Split in two files at mcr-quot's part 12 (size). docs/research/p1-quot.md. -/
'''
docB = docA.replace('helper A', 'helper B').replace('parts 1-11 over the chain', 'parts 12-24 over the chain')

A = ['import ZInQKernel.OneProof.H.TailW', CW + 'ProjectiveLine.Geometry', CW + 'ProjectiveLine.RelativeCoordinates',
     '', docA] + header_lines + partA
B = ['import ZInQKernel.Contrib.OneProof.QuotientP1.MCRQuotA', '', docB] + header_lines + partB
p1 = open(S + 'P1Scheme.lean').read().replace('#print axioms QuotientP1Proof.p1SchemeQ_body\n', '')
p1lines = p1.split('\n')
nimp = sum(1 for l in p1lines if l.startswith('import'))
docP = '''/-!
# p1-quot, helper: the projective line over `ℚ` represents maps to `P¹` by charts

Proves the body of mcr-quot's glue (B-P¹) `P1SchemeQ` (`scratch/mcr-quot/MCRQuot.lean` L8549):
`QuotientP1Proof.p1SchemeQ_body`. `P` is the vendored CloudW07 relative projective line
`ProjectiveSpace (ULift (Fin 2)) (Spec ℚ)` (proper: `ProjectiveSpace.instIsProper`), smooth of relative dimension 1
through its charts `≅ 𝔸¹` (`standardOpenIso`, Mathlib's `AffineSpace.smoothOfRelativeDimension_of_card_eq`), with the
charts `τ.f = T₁/T₀`, `τ.g = T₀/T₁` (`coordRatio`); `ℚ[X] → Γ(chart)` is bijective through
`ℚ[X] ≃ MvPolynomial ≃ Γ(Spec) ≃ Γ(𝔸¹) ≃ Γ(chart)`; a map `σ : ToP1 Z` gives the CloudW07 coordinate cover
`{σ.U, σ.V}` with ratios `1, σ.f, σ.g, 1`, whose morphism `Scheme.CoordinateCover.hom` is the factorization `m`.
docs/research/p1-quot.md. -/
'''
P = p1lines[:nimp] + ['', docP] + p1lines[nimp:]
port3 = open(S + 'Port3.lean').read()
fin = port3[port3.index('/-! ════════════════════════════════════════════════════════════════════════════════════════════\n# p1-quot:'):]
fin = fin[:fin.index('#print axioms')].rstrip() + '\n'
docF = open(S + 'final_doc.md').read()
F = ['import ZInQKernel.Contrib.OneProof.QuotientP1.MCRQuotB',
     'import ZInQKernel.Contrib.OneProof.QuotientP1.P1Scheme',
     'import ZInQKernel.OneProof.H.TailR', '', docF] + header_lines + [fin, 'end HDec', '']
ff = open(S + 'FromFields.lean').read()
ff = ff[:ff.index('#print axioms')].rstrip() + '\n'
import os
os.makedirs(D + 'QuotientP1', exist_ok=True)
for name, L in [('QuotientP1/MCRQuotA.lean', A), ('QuotientP1/MCRQuotB.lean', B), ('QuotientP1/P1Scheme.lean', P),
                ('QuotientP1Coordinate.lean', F), ('QuotientP1/FromFields.lean', ff.split('\n'))]:
    txt = '\n'.join(L).rstrip() + '\n'
    open(D + name, 'w').write(txt)
    print(name, len(txt.encode()))
