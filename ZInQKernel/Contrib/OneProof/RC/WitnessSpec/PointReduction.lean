import ZInQKernel.Contrib.OneProof.RC.Stages.ReducedCurve
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-! Good reduction commutes with Frobenius on coordinates, including at the
point at infinity (tex 8392–8398). -/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open ZInQ.Manuscript.RC.Stages
open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.WitnessSpec

variable {p : ℕ} [Fact p.Prime]
variable {L Γ : Type*} [Field L] [Algebra ℚ L] [DecidableEq L]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
variable {E : WeierstrassCurve ℚ}
  [IsIntegral v.valuationSubring (E⁄L)]
  [(integralModel v.valuationSubring (E⁄L)).IsElliptic]
  [DecidableEq (ResidueField v.valuationSubring)]
  [Algebra (ZMod p) (ResidueField v.valuationSubring)]

local notation "R" => v.valuationSubring
local notation "k" => ResidueField R
local notation "Wℓ" => WeierstrassCurve.toAffine (E⁄L)
local notation "C" => (integralModel R Wℓ)
local notation "Ck" => (WeierstrassCurve.map C (residue R))

variable (B : WeierstrassCurve (ZMod p))

/-- Good reduction, with the target stated using a model over the prime field. -/
def reductionToModel (hB : Ck = (B⁄k)) : Affine.Point Wℓ →+ (B⁄k).toAffine.Point := by
  exact (AddEquiv.cast (M := fun T : WeierstrassCurve k => T.toAffine.Point) hB).toAddMonoidHom.comp
    (Point.reductionHom v (W := Wℓ))

private theorem reductionToModel_some (hB : Ck = (B⁄k)) {x y : L} (hxy : Affine.Nonsingular Wℓ x y)
    (hx : v x ≤ 1) (hy : v y ≤ 1) :
    ∃ h, reductionToModel (E := E) v B hB (.some x y hxy) =
      Point.some (W' := (B⁄k).toAffine) (residue R ⟨x, hx⟩) (residue R ⟨y, hy⟩) h := by
  have h0 : Affine.Equation (WeierstrassCurve.toAffine C) ⟨x, hx⟩ ⟨y, hy⟩ :=
    (equation_integralModel_iff v).mpr hxy.left
  have hh : Affine.Nonsingular (WeierstrassCurve.toAffine Ck) (residue R ⟨x, hx⟩) (residue R ⟨y, hy⟩) :=
    equation_iff_nonsingular.mp (h0.map (residue R))
  refine ⟨hB ▸ hh, ?_⟩
  unfold reductionToModel
  rw [AddMonoidHom.comp_apply,
    Point.reductionHom_some_of_valuation_le_one v hxy hx hh,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.cast_apply]
  exact Point.cast_some hB hh

private theorem reductionToModel_pole (hB : Ck = (B⁄k)) {x y : L} (hxy : Affine.Nonsingular Wℓ x y)
    (hx : 1 < v x) :
    reductionToModel (E := E) v B hB (.some x y hxy) = 0 := by
  unfold reductionToModel
  rw [AddMonoidHom.comp_apply, Point.reductionHom_some_of_one_lt v hxy hx, map_zero]

private theorem fp_frob_apply {K : Type*} [Field K] [Algebra (ZMod p) K] (x : K) :
    FiniteField.frobeniusAlgHom (ZMod p) K x = x ^ p := by
  change x ^ Fintype.card (ZMod p) = _
  rw [ZMod.card]

/-- If a decomposition element acts by the p-th power on integral residues,
good reduction intertwines that element with arithmetic Frobenius on every
point: integral affine coordinates reduce coordinatewise, and poles stay poles. -/
theorem reductionToModel_frobenius (hB : Ck = (B⁄k)) (σ : L ≃ₐ[ℚ] L)
    (hstab : ∀ x, v (σ x) ≤ 1 ↔ v x ≤ 1)
    (hres : ∀ (x : L) (hx : v x ≤ 1), residue R ⟨σ x, (hstab x).mpr hx⟩ =
      (residue R ⟨x, hx⟩) ^ p) (P : Affine.Point Wℓ) :
    reductionToModel (E := E) v B hB (Point.map (W' := E) σ.toAlgHom P) =
      curveFrob (K := k) B (reductionToModel (E := E) v B hB P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · simp only [← Point.zero_def, map_zero]
  · rw [Point.map_some (W' := E) σ.toAlgHom]
    simp only [AlgEquiv.coe_toAlgHom]
    have hσxy : Affine.Nonsingular Wℓ (σ x) (σ y) :=
      (Affine.baseChange_nonsingular E (f := σ.toAlgHom) σ.injective x y).mpr hxy
    by_cases hx : v x ≤ 1
    · have hy := valuation_y_le_one_of_valuation_x_le_one v hxy.left hx
      obtain ⟨_, hp⟩ := reductionToModel_some v B hB hxy hx hy
      obtain ⟨_, hσp⟩ :=
        reductionToModel_some v B hB hσxy ((hstab x).mpr hx) ((hstab y).mpr hy)
      rw [hp, hσp, curveFrob, Point.map_some]
      simp only [fp_frob_apply, hres x hx, hres y hy]
    · rw [reductionToModel_pole v B hB hσxy (not_le.mp (mt (hstab x).mp hx)),
        reductionToModel_pole v B hB _ (not_le.mp hx), map_zero]

/-- An embedding of a field of order p² into a common residue model sends every
point to the square-fixed group used by the detector. -/
def quadraticResiduePoints {k₀ K : Type*} [Field k₀] [Field K]
    [Algebra (ZMod p) k₀] [Algebra (ZMod p) K] [DecidableEq k₀] [DecidableEq K]
    [Finite k₀] (hcard : Nat.card k₀ = p ^ 2) (B : WeierstrassCurve (ZMod p))
    (e : k₀ →ₐ[ZMod p] K) :
    (B⁄k₀).toAffine.Point →+ FixedSq (curveFrob (K := K) B) :=
  (Point.map (W' := B) e).codRestrict _ fun P => by
    apply (mem_fixedSq _).mpr
    cases P with
    | zero => simp only [← Point.zero_def, map_zero]
    | some x y h =>
      let := Fintype.ofFinite k₀
      have he (z : k₀) : ((e z) ^ p) ^ p = e z := by
        have hz := FiniteField.pow_card z
        rw [← Nat.card_eq_fintype_card, hcard, pow_two] at hz
        rw [← pow_mul, ← map_pow e z (p * p), hz]
      simp only [curveFrob, Point.map_some, fp_frob_apply, he]

#print axioms reductionToModel
#print axioms reductionToModel_some
#print axioms reductionToModel_pole
#print axioms fp_frob_apply
#print axioms reductionToModel_frobenius
#print axioms quadraticResiduePoints

end ZInQ.Manuscript.RC.WitnessSpec
