import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Valuation
import Mathlib.Algebra.QuaternionBasis
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.Linarith

/-! The explicit quaternion algebra and its reduced trace and norm.
The coordinate construction is provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalDivision

open QuaternionAlgebra
open scoped QuaternionAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The specified scalar extension of the rational quaternion presentation. -/
abbrev D := QuaternionAlgebra ℚ_[p] (-1) 0 (-(p : ℚ_[p]))

variable {p}

@[simp] theorem scalar_compat (a : ℤ_[p]) :
    algebraMap ℤ_[p] (D p) a = algebraMap ℚ_[p] (D p) (a : ℚ_[p]) := rfl

/-- The coordinates give the product topology. -/
noncomputable instance : TopologicalSpace (D p) :=
  TopologicalSpace.induced (QuaternionAlgebra.equivProd _ _ _ : D p ≃ _) inferInstance

noncomputable def coordHomeomorph : D p ≃ₜ ℚ_[p] × ℚ_[p] × ℚ_[p] × ℚ_[p] where
  toEquiv := QuaternionAlgebra.equivProd _ _ _
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr (by
    change Continuous (fun x : ℚ_[p] × ℚ_[p] × ℚ_[p] × ℚ_[p] =>
      (QuaternionAlgebra.equivProd _ _ _) ((QuaternionAlgebra.equivProd _ _ _).symm x))
    simp only [Equiv.apply_symm_apply]
    exact continuous_id)

instance : T2Space (D p) := (coordHomeomorph (p := p)).isEmbedding.t2Space

theorem rank_four : Module.finrank ℚ_[p] (D p) = 4 :=
  QuaternionAlgebra.finrank_eq_four _ _ _

/-- Reduced trace in the basis 1, i, j, ij. -/
noncomputable def tr : D p →ₗ[ℚ_[p]] ℚ_[p] := (2 : ℚ_[p]) • (QuaternionAlgebra.reₗ _ _ _ : D p →ₗ[ℚ_[p]] ℚ_[p])

@[simp] theorem tr_apply (x : D p) : tr x = 2 * x.re := rfl

theorem tr_continuous : Continuous (tr : D p → ℚ_[p]) := by
  change Continuous (fun x : D p => (2 : ℚ_[p]) * (coordHomeomorph x).1)
  exact continuous_const.mul (coordHomeomorph (p := p)).continuous.fst

theorem tr_mul_comm (x y : D p) : tr (x * y) = tr (y * x) := by
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,h⟩
  simp only [tr_apply, mk_mul_mk]
  ring

theorem tr_conj (u : (D p)ˣ) (x : D p) : tr ((↑u⁻¹ : D p) * x * (u : D p)) = tr x := by
  rw [tr_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

private noncomputable def normValue (x : D p) : ℚ_[p] := (x * star x).re

private theorem mul_star_eq (x : D p) :
    x * star x = algebraMap ℚ_[p] (D p) (normValue x) := x.mul_star_eq_coe

private theorem star_mul_eq (x : D p) :
    star x * x = algebraMap ℚ_[p] (D p) (normValue x) := by
  rw [star_comm_self', mul_star_eq]

/-- The scalar in the product of a quaternion with its conjugate. -/
noncomputable def nrd : D p →* ℚ_[p] where
  toFun := normValue
  map_one' := by simp [normValue]
  map_mul' x y := by
    apply (algebraMap ℚ_[p] (D p)).injective
    rw [← mul_star_eq, map_mul, ← mul_star_eq, ← mul_star_eq, star_mul]
    calc
      x * y * (star y * star x) = x * (y * star y) * star x := by simp only [mul_assoc]
      _ = y * star y * (x * star x) := by
        rw [mul_star_eq y, ← (Algebra.commutes _ x), mul_assoc]
      _ = x * star x * (y * star y) := by
        rw [mul_star_eq y, (Algebra.commutes (normValue y) (x * star x))]

theorem nrd_mul_star (x : D p) :
    x * star x = algebraMap ℚ_[p] (D p) (nrd x) := mul_star_eq x

theorem nrd_formula (x : D p) :
    nrd x = x.re ^ 2 + x.imI ^ 2 + (p : ℚ_[p]) * (x.imJ ^ 2 + x.imK ^ 2) := by
  rcases x with ⟨a,b,c,d⟩
  change ((QuaternionAlgebra.mk a b c d : D p) * QuaternionAlgebra.mk (a + 0*b) (-b) (-c) (-d)).re =
    a ^ 2 + b ^ 2 + (p : ℚ_[p]) * (c ^ 2 + d ^ 2)
  rw [mk_mul_mk]
  change a*(a+0*b) + (-1)*b*(-b) + (-(p : ℚ_[p]))*c*(-c) +
    0 * (-(p : ℚ_[p]))*c*(-d) - (-1)* (-(p : ℚ_[p]))*d*(-d) = _
  ring

theorem nrd_algebraMap (a : ℚ_[p]) : nrd (algebraMap ℚ_[p] (D p) a) = a ^ 2 := by
  simp [nrd_formula, QuaternionAlgebra.algebraMap_eq]

theorem nrd_smul (a : ℚ_[p]) (x : D p) : nrd (a • x) = a ^ 2 * nrd x := by
  rw [Algebra.smul_def, map_mul, nrd_algebraMap]

theorem nrd_continuous : Continuous (nrd : D p → ℚ_[p]) := by
  have h := (coordHomeomorph (p := p)).continuous
  change Continuous (fun x : D p => nrd x)
  simp_rw [nrd_formula]
  exact (h.fst.pow 2).add (h.snd.fst.pow 2) |>.add
      (continuous_const.mul ((h.snd.snd.fst.pow 2).add (h.snd.snd.snd.pow 2)))

theorem nrd_conj (u : (D p)ˣ) (x : D p) :
    nrd ((↑u⁻¹ : D p) * x * (u : D p)) = nrd x := by
  rw [map_mul, map_mul, mul_right_comm, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem tr_zero_sq (x : D p) (h : tr x = 0) :
    algebraMap ℚ_[p] (D p) (nrd x) = -(x ^ 2) := by
  have hr : x.re = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
  rw [← nrd_mul_star, QuaternionAlgebra.star_eq_neg.mpr hr, mul_neg, pow_two]

variable [Fact (p % 4 = 3)]

theorem norm_nrd (x : D p) :
    ‖nrd x‖ = max (max ‖x.re‖ ‖x.imI‖ ^ 2)
      (‖(p : ℚ_[p])‖ * max ‖x.imJ‖ ‖x.imK‖ ^ 2) := by
  rw [nrd_formula, norm_four Fact.out]

theorem nrd_eq_zero (x : D p) : nrd x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h := norm_nrd x
    rw [hx, norm_zero] at h
    have hp : 0 < ‖(p : ℚ_[p])‖ :=
      norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have h₁ : max ‖x.re‖ ‖x.imI‖ ^ 2 ≤ 0 := (le_max_left _ _).trans_eq h.symm
    have h₂ : max ‖x.imJ‖ ‖x.imK‖ ≤ 0 := by
      have hh : ‖(p : ℚ_[p])‖ * max ‖x.imJ‖ ‖x.imK‖ ^ 2 ≤ 0 :=
        (le_max_right _ _).trans_eq h.symm
      have hh' := nonpos_of_mul_nonpos_right hh hp
      nlinarith [le_max_left ‖x.imJ‖ ‖x.imK‖, norm_nonneg x.imJ]
    have h₁' : max ‖x.re‖ ‖x.imI‖ ≤ 0 := by
      nlinarith [le_max_left ‖x.re‖ ‖x.imI‖, norm_nonneg x.re]
    apply QuaternionAlgebra.ext
    · exact norm_le_zero_iff.mp ((le_max_left _ _).trans h₁')
    · exact norm_le_zero_iff.mp ((le_max_right _ _).trans h₁')
    · exact norm_le_zero_iff.mp ((le_max_left _ _).trans h₂)
    · exact norm_le_zero_iff.mp ((le_max_right _ _).trans h₂)
  · rintro rfl
    simp [nrd_formula]

/-- Explicit two-sided inverse for a nonzero quaternion. -/
noncomputable def unitOfNonzero (x : D p) (hx : x ≠ 0) : (D p)ˣ where
  val := x
  inv := algebraMap ℚ_[p] (D p) (nrd x)⁻¹ * star x
  val_inv := by
    rw [← mul_assoc, ← Algebra.commutes (nrd x)⁻¹ x, mul_assoc, nrd_mul_star, ← map_mul,
      inv_mul_cancel₀ (mt (nrd_eq_zero x).mp hx), map_one]
  inv_val := by
    rw [mul_assoc, star_mul_eq, ← map_mul]
    change algebraMap ℚ_[p] (D p) ((nrd x)⁻¹ * nrd x) = 1
    rw [inv_mul_cancel₀ (mt (nrd_eq_zero x).mp hx), map_one]

noncomputable instance : DivisionRing (D p) :=
  DivisionRing.ofIsUnitOrEqZero fun x => by
    by_cases h : x = 0
    · exact .inr h
    · exact .inl ⟨unitOfNonzero x h, rfl⟩

theorem inv_formula (x : D p) (hx : x ≠ 0) :
    x⁻¹ = algebraMap ℚ_[p] (D p) (nrd x)⁻¹ * star x := by
  change ((unitOfNonzero x hx).val)⁻¹ = _
  exact Units.val_inv_eq_inv_val _ |>.symm

#print axioms scalar_compat
#print axioms coordHomeomorph
#print axioms rank_four
#print axioms tr_apply
#print axioms tr_continuous
#print axioms tr_mul_comm
#print axioms tr_conj
#print axioms mul_star_eq
#print axioms star_mul_eq
#print axioms nrd_mul_star
#print axioms nrd_formula
#print axioms nrd_algebraMap
#print axioms nrd_smul
#print axioms nrd_continuous
#print axioms nrd_conj
#print axioms tr_zero_sq
#print axioms norm_nrd
#print axioms nrd_eq_zero
#print axioms unitOfNonzero
#print axioms inv_formula

end ZInQ.Manuscript.RC.LocalDivision
