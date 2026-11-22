/-
Multiplication-etale construction: OriginTangent.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.PowerAtIdentity

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

noncomputable section

namespace H101DirectFieldRoute

universe u

/-- The actual action of multiplication by n+1 on a tangent arrow at the unit.
The membership proof uses the already-written actual arrow identity, not a
new desired naturality Fact. -/
def unitTangentPower {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (s : S) (n : ℕ)
    (θ : DottedTangentArrow G.hom ((η[G]).left s)) :
    DottedTangentArrow G.hom ((η[G]).left s) := by
  refine ⟨θ.val ≫ ((𝟙 G) ^ (n + 1)).left, ?_⟩
  rw [AlgebraicGeometry.comp_pow_id_left_eq_nsmul G s θ n]
  exact ((n + 1) • θ).property

/-- The concrete composition-defined function is exactly scalar multiplication
on the existing tangent space, by the source's actual multiplication proof. -/
theorem unitTangentPower_eq_nsmul {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (s : S) (n : ℕ) (θ : DottedTangentArrow G.hom ((η[G]).left s)) :
    unitTangentPower G s n θ = (n + 1) • θ := by
  exact Subtype.ext (AlgebraicGeometry.comp_pow_id_left_eq_nsmul G s θ n)

/-- Multiplication acts bijectively on the actual tangent arrows at the unit
when the natural index is invertible in the actual residue field. No Smooth,
Flat, Noetherian, characteristic-zero or positive-dimension premise is used. -/
theorem unitTangentPower_bijective {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (s : S) (n : ℕ)
    (hn : IsUnit ((n + 1 : ℕ) : G.left.residueField ((η[G]).left s))) :
    Function.Bijective (unitTangentPower G s n) := by
  let κ := G.left.residueField ((η[G]).left s)
  let c : κ := ((n + 1 : ℕ) : κ)
  have hcast (v : DottedTangentArrow G.hom ((η[G]).left s)) :
      (n + 1) • v = c • v := by
    rw [Nat.cast_smul_eq_nsmul]
  constructor
  · intro v w h
    rw [unitTangentPower_eq_nsmul, unitTangentPower_eq_nsmul,
      hcast, hcast] at h
    exact hn.smul_left_cancel.1 h
  · intro v
    refine ⟨c⁻¹ • v, ?_⟩
    rw [unitTangentPower_eq_nsmul, hcast, smul_smul,
      mul_inv_cancel₀ hn.ne_zero, one_smul]

end H101DirectFieldRoute
