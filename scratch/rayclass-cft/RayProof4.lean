import RayProof3

/-! # rayclass-cft, Part P4: the three fields, the CM data at a representative, `RayClassCM` -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT ShimuraGlue.Ray
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)

/-! ## P4a. Copy (height-glue `part_emb.lean` §Field, Mathlib only): `ℚ`-algebra maps out of a quadratic
field, `r + s y ↦ r + s b` -/

section Field

variable {k : Type} [Field k] [NumberField k]

/-- Every element of a quadratic field is `r + s y` for a non-rational `y`. -/
theorem exists_rat_repr (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) :
    ∃ r s : ℚ, x = r + s * y := by
  have hli : LinearIndependent ℚ ![(1 : k), y] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h
      exact ⟨h, rfl⟩
    · exfalso
      apply hy (-a / t)
      rw [Rat.smul_def, Rat.smul_def, mul_one] at h
      push_cast
      field_simp
      linear_combination h
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [hk])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : k), y]) := hsp ▸ Submodule.mem_top
  have hr : Set.range ![(1 : k), y] = {1, y} := by
    ext z; simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hr] at hx
  obtain ⟨r, t, hrt⟩ := Submodule.mem_span_pair.mp hx
  exact ⟨r, t, by rw [← hrt, Rat.smul_def, Rat.smul_def, mul_one]⟩

theorem repr_unique {y : k} (hy : ∀ r : ℚ, y ≠ r) {r s r' s' : ℚ}
    (h : (r : k) + s * y = r' + s' * y) : r = r' ∧ s = s' := by
  by_cases hs : s = s'
  · subst hs
    refine ⟨?_, rfl⟩
    exact_mod_cast add_right_cancel h
  · exfalso
    apply hy ((r' - r) / (s - s'))
    have hs' : ((s : k) - s') ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hs
    push_cast
    field_simp
    linear_combination h

/-- The coordinates of `x` in the basis `(1, y)`. -/
noncomputable def coord0 (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) : ℚ :=
  (exists_rat_repr hk hy x).choose

noncomputable def coord1 (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) : ℚ :=
  (exists_rat_repr hk hy x).choose_spec.choose

theorem coord_spec (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (x : k) :
    x = (coord0 hk hy x : k) + (coord1 hk hy x : k) * y :=
  (exists_rat_repr hk hy x).choose_spec.choose_spec

theorem coord_eq (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r) (r s : ℚ) :
    coord0 hk hy ((r : k) + s * y) = r ∧ coord1 hk hy ((r : k) + s * y) = s :=
  repr_unique hy (coord_spec hk hy _).symm

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- **The `ℚ`-algebra map `k → A` sending a non-rational `y` (root of `X² + PX + Q`) to a root `b`
of the same polynomial**, `r + s y ↦ r + s b`. -/
noncomputable def liftQuad (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r)
    {P Q : ℚ} (hyq : y * y + P * y + Q = 0) (b : A)
    (hb : b * b + P • b + algebraMap ℚ A Q = 0) : k →ₐ[ℚ] A :=
  let F : k → A := fun x => algebraMap ℚ A (coord0 hk hy x) + coord1 hk hy x • b
  have hF : ∀ r s : ℚ, F ((r : k) + s * y) = algebraMap ℚ A r + s • b := fun r s => by
    simp only [F, (coord_eq hk hy r s).1, (coord_eq hk hy r s).2]
  have hx := coord_spec hk hy
  { toFun := F
    map_one' := by
      have : (1 : k) = ((1 : ℚ) : k) + ((0 : ℚ) : k) * y := by push_cast; ring
      rw [this, hF]; simp
    map_mul' := fun x x' => by
      rw [hx x, hx x']
      set r := coord0 hk hy x; set s := coord1 hk hy x
      set r' := coord0 hk hy x'; set s' := coord1 hk hy x'
      have e : ((r : k) + s * y) * ((r' : k) + s' * y) =
          ((r * r' - s * s' * Q : ℚ) : k) + ((r * s' + r' * s - s * s' * P : ℚ) : k) * y := by
        push_cast; linear_combination (s * s' : k) * hyq
      rw [e, hF, hF, hF]
      have hb' : b * b = -(P • b) - Q • (1 : A) := by
        rw [Algebra.algebraMap_eq_smul_one] at hb
        rw [← sub_eq_zero, ← hb]; abel
      simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one, smul_smul, hb', smul_sub, smul_neg]
      module
    map_zero' := by
      have : (0 : k) = ((0 : ℚ) : k) + ((0 : ℚ) : k) * y := by push_cast; ring
      rw [this, hF]; simp
    map_add' := fun x x' => by
      rw [hx x, hx x']
      have e : ((coord0 hk hy x : k) + coord1 hk hy x * y) +
          ((coord0 hk hy x' : k) + coord1 hk hy x' * y) =
          ((coord0 hk hy x + coord0 hk hy x' : ℚ) : k) +
            ((coord1 hk hy x + coord1 hk hy x' : ℚ) : k) * y := by push_cast; ring
      rw [e, hF, hF, hF, map_add, add_smul]; abel
    commutes' := fun r => by
      have : (algebraMap ℚ k r) = (r : k) + ((0 : ℚ) : k) * y := by simp
      rw [this, hF]; simp }

theorem liftQuad_apply (hk : Module.finrank ℚ k = 2) {y : k} (hy : ∀ r : ℚ, y ≠ r)
    {P Q : ℚ} (hyq : y * y + P * y + Q = 0) (b : A)
    (hb : b * b + P • b + algebraMap ℚ A Q = 0) (r s : ℚ) :
    liftQuad hk hy hyq b hb ((r : k) + s * y) = algebraMap ℚ A r + s • b := by
  show algebraMap ℚ A (coord0 hk hy _) + coord1 hk hy _ • b = _
  rw [(coord_eq hk hy r s).1, (coord_eq hk hy r s).2]

end Field

/-! ## P4b. `ι` over `ℂ` and eigenvalues -/

/-- `ι : B → M₂(ℂ)` as a `ℚ`-algebra map. -/
def iotaC : LeafQM.B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun x := (BPAnalytic.QM.iota x).map (algebraMap ℝ ℂ)
  map_one' := by
    have := iota_algebraMap 1
    rw [map_one] at this
    rw [this]; simp
  map_mul' x y := by rw [iota_mul, Matrix.map_mul]
  map_zero' := by
    have := iota_smul 0 0
    rw [zero_smul] at this
    rw [this]; simp
  map_add' x y := by rw [iota_add, Matrix.map_add]; exact fun a b => map_add _ a b
  commutes' r := by
    rw [iota_algebraMap]
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem iotaC_apply (x : LeafQM.B) : iotaC x = (BPAnalytic.QM.iota x).map (algebraMap ℝ ℂ) := rfl

/-- Eigenvalues of `ι(β)` at `(τ, 1)ᵀ` satisfy the quadratic relations of `β`. -/
theorem eig_rel {β : LeafQM.B} {v : Fin 2 → ℂ} (hv : v 1 = 1) {lam : ℂ}
    (h : Matrix.mulVec (iotaC β) v = lam • v) {P Q : ℚ}
    (hb : β * β + P • β + algebraMap ℚ LeafQM.B Q = 0) : lam * lam + P • lam + algebraMap ℚ ℂ Q = 0 := by
  have h0 := congrArg (fun x => Matrix.mulVec (iotaC x) v) hb
  simp only [map_add, map_mul, map_smul, AlgHom.commutes, map_zero, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.zero_mulVec] at h0
  have h1 := congrFun h0 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, Pi.zero_apply] at h1
  rw [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal] at h1
  simp only [Pi.algebraMap_apply, hv, mul_one] at h1
  rw [Rat.smul_def, ← h1]
  simp [Algebra.smul_def]

end RayClassCFT
