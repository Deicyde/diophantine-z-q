import ZInQKernel.OneProof.H.TailY

/-! pazuki-dict: verbatim copy of `ZInQ.HeightSplit.PazukiCor13Upper` (`ZInQKernel/OneProof/H/TailY.lean`, lines
775-787 at 2880fef1), with the `open` lines of its section, checked equal to the original by `rfl`. -/

namespace PazukiDictCopy

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.H5Neron
open ZInQ.LeafPush2 (CPts IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight
  pazukiC2)
open ZInQ.HeightSplit (IsStableFaltingsHeight absLogHeightL2)

/-- **Leaf R22-Pazuki, upper half** (read off the same display as `PazukiCor13`, the side of the
absolute value that bounds `H_Θ` from above): `H_Θ − H_D/2 ≤ C₂ log(min(H_Θ, H_D) + 2)`. The row
needs only this half. -/
def PazukiCor13Upper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ (F : Type) [Field F] [NumberField F] (emb : F →+* ℂ) (z : Char2 → F) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      max 1 (absLogHeightL2 z) - max 1 (x + Real.log Real.pi) / 2 ≤
        pazukiC2 * Real.log (min (max 1 (absLogHeightL2 z)) (max 1 (x + Real.log Real.pi)) + 2)

example : PazukiCor13Upper = ZInQ.HeightSplit.PazukiCor13Upper := rfl

end PazukiDictCopy
