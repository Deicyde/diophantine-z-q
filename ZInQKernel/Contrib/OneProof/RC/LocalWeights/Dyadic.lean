import ZInQKernel.Contrib.OneProof.RC.LocalWeights.LevelSupport
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.SplitAmbient
import Mathlib.FieldTheory.Finite.Basic

/-! The dyadic support when (2∤N) (tex 8517–8534). In characteristic two,
the trace-one characteristic polynomial splits exactly when its determinant
is zero modulo two (provenance (c)). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local notation "red₂" => (PadicInt.toZModPow 1 : ℤ_[2] →+* ZMod 2)

theorem dyadicUnit_red (v : ℤ_[2]ˣ) : red₂ v.val = 1 := by
  have h := (v.isUnit.map red₂).ne_zero
  generalize red₂ v.val = a at *
  fin_cases a
  · exact False.elim (h rfl)
  · rfl

/-- The two complementary projectors remain distinct after reduction modulo two. -/
theorem dyadic_projectors_distinct {e : ℕ} (P : eichler 2 e) :
    redMat 2 1 P.val ≠ redMat 2 1 (1 - P).val := by
  intro hp
  have h := congrFun (congrFun hp 0) 0
  change red₂ (P.val 0 0) = red₂ (((1 : Mat ℤ_[2]) - P.val) 0 0) at h
  have hn (a : ZMod 2) : a ≠ 1 - a := by
    fin_cases a
    · change (0 : ZMod 2) ≠ 1 - 0
      simp
    · change (1 : ZMod 2) ≠ 1 - 1
      simp
  exact hn _ (by simpa [Matrix.sub_apply, Matrix.one_apply] using h)

/-- No quotient selection is needed. A simple root exists iff the determinant is even. -/
theorem dyadic_split_iff {e : ℕ} (y : eichler 2 e) :
    SplitSupport y ↔ red₂ y.val.det = 0 := by
  constructor
  · rintro ⟨a, ha, -⟩
    have h := congrArg red₂ ha
    simp only [map_add, map_sub, map_pow, map_zero, ZMod.pow_card (p := 2) (red₂ a),
      sub_self, zero_add] at h
    exact h
  · intro h
    have hu : IsUnit (2 * (0 : ℤ_[2]) - 1) := by simp
    obtain ⟨a, ha, -, hau⟩ := lift_branch hu (by simpa using h)
    exact ⟨a, ha, hau⟩

/-- The integral affine weight at two when the level is odd. -/
noncomputable def dyadicWeight {O : Type*} [Zero O] [One O] (y : eichler 2 0) : O :=
  open Classical in
  if red₂ y.val.det = 0 then 1 else 0

theorem dyadicWeight_congr {O : Type*} [Zero O] [One O] (y z : eichler 2 0)
    (h : redMat 2 1 y.val = redMat 2 1 z.val) :
    (dyadicWeight y : O) = dyadicWeight z := by
  have he (i j : Fin 2) : red₂ (y.val i j) = red₂ (z.val i j) :=
    congrFun (congrFun h i) j
  have hd : red₂ y.val.det = red₂ z.val.det := by
    simp only [Matrix.det_fin_two, map_sub, map_mul, he]
  simp only [dyadicWeight, hd]

theorem dyadicWeight_conj {O : Type*} [Zero O] [One O] (u : (eichler 2 0)ˣ) (y : eichler 2 0) :
    dyadicWeight ((↑u⁻¹ : eichler 2 0) * y * (↑u : eichler 2 0)) = (dyadicWeight y : O) := by
  let v : (Mat ℤ_[2])ˣ := Units.map (eichler 2 0).val.toMonoidHom u
  have hd : ((↑u⁻¹ : eichler 2 0) * y * (↑u : eichler 2 0)).val.det = y.val.det :=
    Matrix.det_units_conj' v y.val
  simp only [dyadicWeight, hd]

theorem dyadicWeight_scale {O : Type*} [Zero O] [One O] (v : ℤ_[2]ˣ) (t : ℤ_[2])
    (y : AffineOrder 2 0) : dyadicWeight (affine v.val t y.val) = (dyadicWeight y.val : O) := by
  have ht : red₂ t + red₂ t = 0 := by
    rw [← two_mul]
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  have hd : red₂ (affine v.val t y.val).val.det = red₂ y.val.val.det := by
    rw [affine_det _ _ y.property]
    simp only [map_add, map_mul, map_pow, dyadicUnit_red, one_pow, one_mul, ZMod.pow_card (p := 2) (red₂ t)]
    rw [add_assoc, ht, add_zero]
  simp only [dyadicWeight, hd]

/-- At (2∤N) the support is still the split dyadic support, with weight 1. -/
noncomputable def dyadicSchwartz {O : Type*} [Zero O] [One O] : TraceZero ℚ_[2] → O :=
  extendWeight (affineZero 2 (e := 0)) fun y => dyadicWeight y.val

theorem dyadicSchwartz_compactOpen {O : Type*} [Zero O] [One O] :
    IsLocallyConstant (dyadicSchwartz : TraceZero ℚ_[2] → O) ∧
      IsCompact (Function.support (dyadicSchwartz : TraceZero ℚ_[2] → O)) ∧
      IsOpen (Function.support (dyadicSchwartz : TraceZero ℚ_[2] → O)) := by
  have := affineOrder_compactSpace 2 0
  refine extendWeight_compactOpen (affineZero_openEmbedding 2 0) ?_
  exact locallyConstant_of_factors
    ((redMat_locallyConstant 2 1).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val))
    (fun x y h => dyadicWeight_congr x.val y.val h)

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms dyadicUnit_red
#print axioms dyadic_projectors_distinct
#print axioms dyadic_split_iff
#print axioms dyadicWeight_congr
#print axioms dyadicWeight_conj
#print axioms dyadicWeight_scale
#print axioms dyadicSchwartz_compactOpen
