import ZInQKernel.Contrib.CloudB3W17GAGA.AtlasTransport
import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge

/-!
# Cω fidelity of the actual complex-point carrier comparison

This uses CloudB3W17Hodge's committed classical topology, point equivalence,
and choice-based `chartedSpace` unchanged. It adds only the Cω comparison
maps and their bundled diffeomorphism, usable by H103 without importing the
H105 target or the quotient-descent modules.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17GAGA

local instance comparisonTopology (X : Over (Spec (CommRingCat.of ℂ))) :
    TopologicalSpace (CloudB3W17Hodge.CPt X) := CloudB3W17Hodge.classicalTopology X

local instance comparisonChartedSpace (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] : ChartedSpace (Fin n → ℂ) (CloudB3W17Hodge.CPt X) :=
  CloudB3W17Hodge.chartedSpace X n

/-- The existing carrier comparison is Cω in the committed transported canonical atlas. -/
theorem contMDiff_cptHomeomorph (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (CloudB3W17Hodge.cptHomeomorph X) :=
  contMDiff_homeomorph_transported (CloudB3W17Hodge.cptHomeomorph X)

/-- Its inverse is Cω in exactly the same committed canonical atlas. -/
theorem contMDiff_cptHomeomorph_symm (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (CloudB3W17Hodge.cptHomeomorph X).symm :=
  contMDiff_homeomorph_symm_transported (CloudB3W17Hodge.cptHomeomorph X)

/-- The actual kernel/native carrier equivalence is a genuine biholomorphism. -/
def cptDiffeomorph (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] :
    CloudB3W17Hodge.CPt X ≃ₘ^ω⟮𝓘(ℂ, Fin n → ℂ), 𝓘(ℂ, Fin n → ℂ)⟯ ComplexPoint X where
  toEquiv := CloudB3W17Hodge.cptEquiv X
  contMDiff_toFun := contMDiff_cptHomeomorph X n
  contMDiff_invFun := contMDiff_cptHomeomorph_symm X n

@[simp]
theorem cptDiffeomorph_apply (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (P : CloudB3W17Hodge.CPt X) :
    cptDiffeomorph X n P = CloudB3W17Hodge.cptEquiv X P := rfl

@[simp]
theorem cptDiffeomorph_symm_apply (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (P : ComplexPoint X) :
    (cptDiffeomorph X n).symm P = (CloudB3W17Hodge.cptEquiv X).symm P := rfl

end ZInQ.Contrib.CloudB3W17GAGA
