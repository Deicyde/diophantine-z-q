import ZInQKernel.Contrib.OneProof.HeckeGlue

/-! Verbatim copies of hecke-pin's three Props (from `ZInQKernel/Contrib/OneProof/HeckePin.lean`)
and checks that the copies are the originals (`Iff.rfl`), and that `HeckeGlue` proves exactly them. -/

namespace AfTateLam.HeckeGlueTarget

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open AfTateLam.HeckePin (IsPrimitive)

def X1TauPoints : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX → ∀ τ : UpperHalfPlane, ∃ x : CPt X, AtTau N jX tX x τ

def AbelJacobiX1 : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (f : CF N 2) (F : UpperHalfPlane → ℂ), IsPrimitive f F →
      ∃ Λ : Set ℂ, Λ.Countable ∧
        ∀ (E : UpperHalfPlane →₀ ℤ) (x : UpperHalfPlane → CPt X), (∀ τ, AtTau N jX tX (x τ) τ) →
          (E.sum fun _ n => n) = 0 → (E.prod fun τ n => ajC aj (x τ) ^ n) = 1 →
          (E.sum fun τ n => (n : ℂ) * F τ) ∈ Λ

def ConstOnTauPoints : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX → ∀ (P₀ : RatPt X) (J : AbVar ℚ) (g : X ⟶ J.X), P₀ ≫ g = 1 →
      (∀ (τ τ' : UpperHalfPlane) (x x' : CPt X), AtTau N jX tX x τ → AtTau N jX tX x' τ' → x ≫ g = x' ≫ g) →
      g = 1

theorem copies_eq : (X1TauPoints ↔ HeckePin.X1TauPoints) ∧ (AbelJacobiX1 ↔ HeckePin.AbelJacobiX1) ∧
    (ConstOnTauPoints ↔ HeckePin.ConstOnTauPoints) := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem x1TauPoints_copy : X1TauPoints := HeckeGlue.x1TauPoints

theorem constOnTauPoints_copy : ConstOnTauPoints := HeckeGlue.constOnTauPoints

end AfTateLam.HeckeGlueTarget

#print axioms AfTateLam.HeckeGlueTarget.x1TauPoints_copy
#print axioms AfTateLam.HeckeGlueTarget.constOnTauPoints_copy
