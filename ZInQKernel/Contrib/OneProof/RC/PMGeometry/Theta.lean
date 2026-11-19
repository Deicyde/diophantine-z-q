import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Geometry
import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Evaluation
import ZInQKernel.Contrib.OneProof.RC.PM.Theta

/-! The two theta records, with the derived Geometry and the detector at the chosen place. -/

noncomputable section

open scoped WeierstrassCurve Classical
open TauCeti WeierstrassCurve
open ZInQ.Contrib.ChebFD.C10 (GQ)

namespace ZInQ.Manuscript.RC.PMGeometry

open Eichler WitnessSpec Stages PrintsArith GlueSweep.Tate

variable {a b : ℚ} {R : Order a b} {g σ : GQ} {p N : ℕ} [Fact p.Prime]
  (v : FrobeniusPlace g p) (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic]
  (hg : ¬ (p : ℤ) ∣ C.Δ) (hodd : p ≠ 2) (M : ℕ)
  (hagree : ∀ x ∈ torsField (C⁄ℚ) M, g x = σ x)
  (row : TateMod (C⁄ℚ) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hrow : ∀ t, row (tateRep (C⁄ℚ) 2 σ t) = row t)
  (hsq : tateRep (C⁄ℚ) 2 (σ * σ) = 1)
  {A : Adelic (ell := p) (N := N) R} {ap : ℕ → ℤ}
  (G : GeometricInput A (ResidueAt v) (ReducedEquation C p) ap)
  (L : ℕ) [e : (ReducedEquation C p).IsElliptic]
  {O : Type*} [CommRing O]

/-- The App F theta stage at the chosen place. The existing constructor takes the
norm characters, local theta sums and frame inputs. -/
abbrev appFStage :=
  PM.appFStage (O := O) G.geometry (evaluationAt v C hg hodd M hagree row hrow hsq) L

/-- The visibility theta stage at the same place, with the existing inputs for
the Schwartz weight and an integer lift of the same finite function. -/
abbrev visibilityStage :=
  PM.visibilityStage (O := O) G.geometry (evaluationAt v C hg hodd M hagree row hrow hsq) L

#print axioms appFStage
#print axioms visibilityStage

end ZInQ.Manuscript.RC.PMGeometry
