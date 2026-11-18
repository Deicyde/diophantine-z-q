import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Dyadic
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Product
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Transport
import Mathlib.Tactic.Abel

/-! The actions on the full rational split models, tex 8498, 8512–8515,
8527–8534, 8546–8549 and 8573–8577. Transport formulas are provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix

section MatrixActions
variable {A : Type*} [CommRing A]

def matrixConj (u : (Mat A)ˣ) (x : TraceZero A) : TraceZero A :=
  ⟨(↑u⁻¹ : Mat A) * x.val * (u : Mat A), (trace_units_conj' u x.val).trans x.property⟩

def matrixScale (v : Aˣ) (x : TraceZero A) : TraceZero A :=
  ⟨v.val • x.val, by rw [trace_smul, x.property, smul_zero]⟩

theorem matrixConj_inverse (u : (Mat A)ˣ) :
    Function.LeftInverse (matrixConj u⁻¹) (matrixConj u) := by
  intro x
  apply Subtype.ext
  change (↑u⁻¹⁻¹ : Mat A) * ((↑u⁻¹ : Mat A) * x.val * (u : Mat A)) * (↑u⁻¹ : Mat A) = x.val
  simp only [inv_inv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
    ← Matrix.mul_assoc (u : Mat A) (↑u⁻¹ : Mat A) x.val, Matrix.one_mul]

theorem matrixScale_inverse (v : Aˣ) :
    Function.LeftInverse (matrixScale v⁻¹) (matrixScale v) := by
  intro x
  apply Subtype.ext
  change (↑v⁻¹ : A) • (v.val • x.val) = x.val
  rw [smul_smul, Units.inv_mul, one_smul]
end MatrixActions

variable {p : ℕ} [Fact p.Prime] {e : ℕ}
variable {O : Type*} [CommRing O]

theorem integralMat_smul (a : ℤ_[p]) (x : Mat ℤ_[p]) :
    integralMat p (a • x) = (a : ℚ_[p]) • integralMat p x := by
  apply Matrix.ext
  intro i j
  change ((a * x i j : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) * (x i j : ℚ_[p])
  exact PadicInt.coe_mul _ _

theorem integralMat_scalar (a : ℤ_[p]) :
    integralMat p (algebraMap ℤ_[p] (Mat ℤ_[p]) a) = (a : ℚ_[p]) • (1 : Mat ℚ_[p]) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [integralMat, Matrix.algebraMap_matrix_apply]
  · simp [integralMat, Matrix.algebraMap_matrix_apply, h]

theorem integralZero_conj (u : (Mat ℤ_[p])ˣ) (x : TraceZero ℤ_[p]) :
    matrixConj (Units.map (integralMat p).toMonoidHom u) (integralZero p x) =
      integralZero p (matrixConj u x) := by
  apply Subtype.ext
  change integralMat p (↑u⁻¹ : Mat ℤ_[p]) * integralMat p x.val * integralMat p (u : Mat ℤ_[p]) =
    integralMat p ((↑u⁻¹ : Mat ℤ_[p]) * x.val * (u : Mat ℤ_[p]))
  rw [map_mul, map_mul]

theorem integralZero_scale (v : ℤ_[p]ˣ) (x : TraceZero ℤ_[p]) :
    matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v) (integralZero p x) =
      integralZero p (matrixScale v x) :=
  Subtype.ext (integralMat_smul v.val x.val).symm

theorem goodWeight_extend :
    (goodWeight p : TraceZero ℚ_[p] → O) = extendWeight (integralZero p) (fun _ => 1) := by
  funext x
  classical
  have hs := extendWeight_spec (integralZero p) (fun _ => (1 : O))
    (integralZero_openEmbedding p).injective
  have hr : x ∈ Set.range (integralZero p) ↔ ∀ i j, x.val i j ∈ PadicInt.subring p := by
    constructor
    · rintro ⟨a, rfl⟩ i j
      exact (a.val i j).property
    · intro h
      let a : Mat ℤ_[p] := fun i j => ⟨x.val i j, h i j⟩
      have ha : integralMat p a = x.val := rfl
      have ht : a.trace = 0 := PadicInt.coe_eq_zero.mp (by
        rw [← integralMat_trace, ha, x.property])
      exact ⟨⟨a, ht⟩, Subtype.ext ha⟩
  by_cases h : x ∈ Set.range (integralZero p)
  · rw [goodWeight, ite_eq_left (hr.mp h)]
    obtain ⟨y, rfl⟩ := h
    exact (hs.1 _).symm
  · rw [goodWeight, ite_eq_right (mt hr.mpr h), hs.2 _ h]

/-- The two trivial multipliers at a good prime. -/
noncomputable def goodRule : LocalRule (O := O) (TraceZero ℚ_[p]) (GL (Fin 2) ℤ_[p]) ℤ_[p]ˣ where
  weight := goodWeight p
  conj u := matrixConj (Units.map (integralMat p).toMonoidHom u)
  scale v := matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v)
  norm := GeneralLinearGroup.det
  normChar := 1
  alpha := 1
  weight_conj u x := by
    simp only [MonoidHom.one_apply, inv_one, Units.val_one]
    rw [goodWeight_extend]
    exact extendWeight_transform _ (integralZero_openEmbedding p).injective _ 1
      _ (matrixConj u) (matrixConj (Units.map (integralMat p).toMonoidHom u⁻¹)) (matrixConj u⁻¹)
      (by rw [map_inv]; exact matrixConj_inverse _)
      (integralZero_conj u) (integralZero_conj u⁻¹)
      (fun _ => (one_mul _).symm) x
  weight_scale v x := by
    simp only [MonoidHom.one_apply, Units.val_one]
    rw [goodWeight_extend]
    exact extendWeight_transform _ (integralZero_openEmbedding p).injective _ 1
      _ (matrixScale v)
      (matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v⁻¹)) (matrixScale v⁻¹)
      (by rw [map_inv]; exact matrixScale_inverse _)
      (integralZero_scale v) (integralZero_scale v⁻¹)
      (fun _ => (one_mul _).symm) x

/-- The two Legendre multipliers at a prime dividing (m). -/
noncomputable def nilRule : LocalRule (O := O) (TraceZero ℚ_[p]) (GL (Fin 2) ℤ_[p]) ℤ_[p]ˣ where
  weight := nilSchwartz p
  conj u := matrixConj (Units.map (integralMat p).toMonoidHom u)
  scale v := matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v)
  norm := GeneralLinearGroup.det
  normChar := legendreUnit p
  alpha := legendreUnit p
  weight_conj u x := by
    rw [legendreUnit_inv, legendreUnit_apply]
    exact extendWeight_transform _ (integralZero_openEmbedding p).injective _ _
      _ (matrixConj u) (matrixConj (Units.map (integralMat p).toMonoidHom u⁻¹)) (matrixConj u⁻¹)
      (by rw [map_inv]; exact matrixConj_inverse _)
      (integralZero_conj u) (integralZero_conj u⁻¹)
      (nilWeight_conj u) x
  weight_scale v x := by
    rw [legendreUnit_apply]
    exact extendWeight_transform _ (integralZero_openEmbedding p).injective _ _
      _ (matrixScale v)
      (matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v⁻¹)) (matrixScale v⁻¹)
      (by rw [map_inv]; exact matrixScale_inverse _)
      (integralZero_scale v) (integralZero_scale v⁻¹)
      (nilWeight_scale v) x

noncomputable def eichlerUnit : (eichler p e)ˣ →* (Mat ℤ_[p])ˣ :=
  Units.map (eichler p e).val.toMonoidHom

noncomputable def affineConj (u : (eichler p e)ˣ) (y : AffineOrder p e) : AffineOrder p e :=
  ⟨(↑u⁻¹ : eichler p e) * y.val * (↑u : eichler p e),
    (trace_units_conj' (eichlerUnit u) y.val.val).trans y.property⟩

noncomputable def affineScale (v : ℤ_[p]ˣ) (y : AffineOrder p e) : AffineOrder p e :=
  ⟨affine v.val (affine_offset v).choose y.val,
    affine_trace v.val _ (affine_offset v).choose_spec y.val y.property⟩

theorem affineZero_conj (u : (eichler p e)ˣ) (y : AffineOrder p e) :
    matrixConj (Units.map (integralMat p).toMonoidHom (eichlerUnit u)) (affineZero p y) =
      affineZero p (affineConj u y) := by
  let U : (Mat ℚ_[p])ˣ := Units.map (integralMat p).toMonoidHom (eichlerUnit u)
  apply Subtype.ext
  change (↑U⁻¹ : Mat ℚ_[p]) * ((2 : ℚ_[p]) • integralMat p y.val.val - 1) * (U : Mat ℚ_[p]) =
    (2 : ℚ_[p]) • integralMat p ((↑u⁻¹ : eichler p e).val * y.val.val * (↑u : eichler p e).val) - 1
  simp only [map_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.mul_one, Units.inv_mul]
  rfl

theorem affineZero_scale (v : ℤ_[p]ˣ) (y : AffineOrder p e) :
    matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v) (affineZero p y) =
      affineZero p (affineScale v y) := by
  let t := (affine_offset v).choose
  have ht : (2 : ℚ_[p]) * (t : ℚ_[p]) = 1 - (v.val : ℚ_[p]) := by
    exact congrArg (PadicInt.Coe.ringHom (p := p)) (affine_offset v).choose_spec
  apply Subtype.ext
  change (v.val : ℚ_[p]) • ((2 : ℚ_[p]) • integralMat p y.val.val - 1) =
    (2 : ℚ_[p]) • integralMat p
      (v.val • y.val.val + algebraMap ℤ_[p] (Mat ℤ_[p]) t) - 1
  rw [map_add, integralMat_smul, integralMat_scalar, smul_add, smul_sub, smul_smul, smul_smul,
    smul_smul, mul_comm (v.val : ℚ_[p]), ht, sub_smul, one_smul]
  abel

/-- The positive-level local rules, for either odd level or dyadic level. -/
noncomputable def levelRule (he : 0 < e) {k : ℕ} (χ : (ZMod (p ^ k))ˣ →* Oˣ) :
    LocalRule (O := O) (TraceZero ℚ_[p]) (eichler p e)ˣ ℤ_[p]ˣ where
  weight := levelSchwartz p χ
  conj u := matrixConj (Units.map (integralMat p).toMonoidHom (eichlerUnit u))
  scale v := matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v)
  norm := GeneralLinearGroup.det.comp eichlerUnit
  normChar := 1
  alpha := χ.comp (Units.map (PadicInt.toZModPow k : ℤ_[p] →+* _).toMonoidHom)
  weight_conj u x := by
    simp only [MonoidHom.one_apply, inv_one, Units.val_one]
    exact extendWeight_transform _ (affineZero_openEmbedding p e).injective _ 1
      _ (affineConj u)
      (matrixConj (Units.map (integralMat p).toMonoidHom (eichlerUnit u⁻¹))) (affineConj u⁻¹)
      (by rw [map_inv, map_inv]; exact matrixConj_inverse _)
      (affineZero_conj u) (affineZero_conj u⁻¹)
      (fun y => (levelWeight_conj he _ u y.val).trans (one_mul _).symm) x
  weight_scale v x := by
    exact extendWeight_transform _ (affineZero_openEmbedding p e).injective _ _
      _ (affineScale v)
      (matrixScale (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v⁻¹)) (affineScale v⁻¹)
      (by rw [map_inv]; exact matrixScale_inverse _)
      (affineZero_scale v) (affineZero_scale v⁻¹)
      (fun y => levelWeight_scale he _ v _ (affine_offset v).choose_spec y.val y.property) x

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The dyadic local rules at odd global level: both multipliers are trivial. -/
noncomputable def dyadicRule :
    LocalRule (O := O) (TraceZero ℚ_[2]) (eichler 2 0)ˣ ℤ_[2]ˣ where
  weight := dyadicSchwartz
  conj u := matrixConj (Units.map (integralMat 2).toMonoidHom (eichlerUnit u))
  scale v := matrixScale (Units.map (PadicInt.Coe.ringHom (p := 2)).toMonoidHom v)
  norm := GeneralLinearGroup.det.comp eichlerUnit
  normChar := 1
  alpha := 1
  weight_conj u x := by
    simp only [MonoidHom.one_apply, inv_one, Units.val_one]
    exact extendWeight_transform _ (affineZero_openEmbedding 2 0).injective _ 1
      _ (affineConj u)
      (matrixConj (Units.map (integralMat 2).toMonoidHom (eichlerUnit u⁻¹))) (affineConj u⁻¹)
      (by rw [map_inv, map_inv]; exact matrixConj_inverse _)
      (affineZero_conj u) (affineZero_conj u⁻¹)
      (fun y => (dyadicWeight_conj u y.val).trans (one_mul _).symm) x
  weight_scale v x := by
    simp only [MonoidHom.one_apply, Units.val_one]
    exact extendWeight_transform _ (affineZero_openEmbedding 2 0).injective _ 1
      _ (affineScale v)
      (matrixScale (Units.map (PadicInt.Coe.ringHom (p := 2)).toMonoidHom v⁻¹)) (affineScale v⁻¹)
      (by rw [map_inv]; exact matrixScale_inverse _)
      (affineZero_scale v) (affineZero_scale v⁻¹)
      (fun y => (dyadicWeight_scale v _ y).trans (one_mul _).symm) x

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms matrixConj_inverse
#print axioms matrixScale_inverse
#print axioms integralMat_smul
#print axioms integralMat_scalar
#print axioms integralZero_conj
#print axioms integralZero_scale
#print axioms goodWeight_extend
#print axioms goodRule
#print axioms nilRule
#print axioms affineZero_conj
#print axioms affineZero_scale
#print axioms levelRule
#print axioms dyadicRule
