import ZInQKernel.Contrib.OneProof.EigenformHTWeak

/-! # ht-exists: the field `eigenformHTNew` from Kato's theorem in its existence form

Task ht-exists, 2026-11-15 (report `docs/research/ht-exists.md`, log `scratch/ht-exists/log.md`).

The open field `eigenformHTNew : ZInQ.Contrib.HodgeSplit.EigenformHTNew` says: **every** semisimple
`ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to a newform `f` of weight `k ≥ 2` (trace form `AttachedTo`: arithmetic
Frobenius, trace `a_p`) has Hodge–Tate weights `{0, 1 − k}` at `ℓ`. The printed theorem (Kato 2004, §§9.2-9.4,
with Faltings 1987 / Scholl 1990 / Saito 1997 as alternatives) is about **the** representation the source
constructs, `V_{F_λ}(f)` (cohomological normalization: geometric Frobenius has trace `a_p`, Hodge–Tate weights
`{0, k − 1}`). This file states that theorem in its existence form and proves the field from it.

* §1-§5: the contragredient `dualGR` and the glue `HTDual` (Hodge–Tate weights of `ρ^∨` are `−S`), proved from
  the bundle LEAF fields `tateTwistInvariants`, `axSenTate` (Tate 1967 §3.3 Thms 1-2). Copied verbatim from
  `scratch/c-to-printed2/HTDual.lean` (namespace renamed).
* §6: the contragredient of a semisimple representation is semisimple (copied from c-to-printed2).
* §7: the new leaf `KatoHTExists` (existence form, cohomological normalization, semisimple witness) and
  `eigenformHTNew_of_katoHTExists : KatoHTExists → TateTwistInvariants → AxSenTate → EigenformHTNew`: dualize the
  witness (`HTDual`), then transport to every semisimple attached `ρ` by Chebotarev + Brauer–Nesbitt
  (the kernel's `attachedConj_proof`, from T18 and T19) and the invariance of Hodge–Tate weights under
  conjugation (the kernel's `htConj_proof`). Converse `katoHTExists_of_eigenformHTNew` (with the LEAF fields
  `dsThm965`, `dsThm966`): the leaf is no stronger than the field.
* §8: the instance the route uses (ht-bypass: `ℓ = 5`, `k ≥ 3`): `KatoHTExists5Ge3 → EigenformHTNew5Ge3`, its
  converse, and the consumer input `G0Galois.EigenformHT5Ge3Chain` of `afterG7_of3Weak`.

No `sorry`, no `axiom`, no code that runs at build time.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace EigenformHTExists

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

/-! ## §1. The contragredient (modular-split's `EigenHT.lean` §Dual, verbatim) -/

section Dual

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

theorem mat_mul_inv (ρ : GaloisRep ℓ n) (σ : GQ) :
    ρ.mat σ * ρ.mat σ⁻¹ = 1 := by
  rw [GaloisRep.mat, GaloisRep.mat, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mat_inv_mul (ρ : GaloisRep ℓ n) (σ : GQ) :
    ρ.mat σ⁻¹ * ρ.mat σ = 1 := by
  rw [GaloisRep.mat, GaloisRep.mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

/-- The contragredient `ρ^∨(σ) = ρ(σ⁻¹)ᵀ` as a homomorphism. -/
noncomputable def dualHom (ρ : GaloisRep ℓ n) : GQ →* GL (Fin n) (PadicAlgCl ℓ) where
  toFun σ := ⟨(ρ.mat σ⁻¹).transpose, (ρ.mat σ).transpose,
    by rw [← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp [GaloisRep.mat])
  map_mul' σ τ := Units.ext (by
    simp only [GaloisRep.mat, mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul])

/-- **The contragredient** `ρ^∨(σ) = ρ(σ⁻¹)ᵀ` of a continuous representation. -/
noncomputable def dualGR (ρ : GaloisRep ℓ n) : GaloisRep ℓ n where
  toHom := dualHom ρ
  continuous_toHom := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous fun σ : GQ => (ρ.mat σ⁻¹).transpose
      exact ((Units.continuous_val.comp ρ.continuous_toHom).comp continuous_inv).matrix_transpose
    · change Continuous fun σ : GQ => (ρ.mat σ).transpose
      exact (Units.continuous_val.comp ρ.continuous_toHom).matrix_transpose

theorem dualGR_mat (ρ : GaloisRep ℓ n) (σ : GQ) : (dualGR ρ).mat σ = (ρ.mat σ⁻¹).transpose := rfl

end Dual

/-- **GLUE `HTDual` (modular-split, verbatim): Hodge–Tate weights of the contragredient.** If `ρ|_{G_{ℚ_ℓ}}` is
Hodge–Tate with weight multiset `S` (`card S = n`), then `ρ^∨|_{G_{ℚ_ℓ}}` is Hodge–Tate with weights `−S`.
Proved below (`htDual_proof`) from the bundle leaves `TateTwistInvariants` and `AxSenTate`. -/
def HTDual : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (ρ : GaloisRep ℓ n) (S : Multiset ℤ), S.card = n →
    ρ.HasHTWeightsAtSelf ℓ S → (dualGR ρ).HasHTWeightsAtSelf ℓ (S.map Neg.neg)

/-! ## §2. Pairing `Y_i(ρ)` with `Y_j(ρ^∨)` -/

section Pairing

variable (p : ℕ) [Fact p.Prime] {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `ρ'` is the contragredient of `ρ`, read in `ℂ_p`: `ρ'(σ)ᵀ = ρ(σ⁻¹)`. -/
def IsDualPair (ρ ρ' : GQp p →* GL (Fin n) E) : Prop :=
  ∀ σ, (matC p (ρ' σ : Matrix (Fin n) (Fin n) E)).transpose = matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)

theorem IsDualPair.symm {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') : IsDualPair p ρ' ρ := by
  intro σ
  have h1 := h σ⁻¹
  rw [inv_inv] at h1
  rw [← h1, Matrix.transpose_transpose]

theorem cpAct_dot (σ : GQp p) (y z : Fin n → ℂ_[p]) :
    cpAct p σ (y ⬝ᵥ z) = vAct p σ y ⬝ᵥ vAct p σ z := by
  simp only [dotProduct, map_sum, map_mul, vAct]

/-- **Step 1: the twist of the pairing.** -/
theorem pair_twist {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {i j : ℤ}
    {y z : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i E) (hz : z ∈ Ysp p ρ' j E) {σ : GQp p}
    (hσ : σ ∈ E.fixingSubgroup) :
    cycPow p σ (i + j) • cpAct p σ (y ⬝ᵥ z) = y ⬝ᵥ z := by
  have h1 := hy σ hσ
  have h2 := hz σ hσ
  rw [h σ] at h2
  rw [cpAct_dot, cycPow_add, mul_smul, ← dotProduct_smul, ← smul_dotProduct, ← h1, ← h2,
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, matC_mul_inv,
    Matrix.one_mulVec]

theorem pair_eq_zero (hT : TateTwistInvariants) [FiniteDimensional ℚ_[p] E]
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {i j : ℤ} (hij : i + j ≠ 0)
    {y z : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i E) (hz : z ∈ Ysp p ρ' j E) : y ⬝ᵥ z = 0 :=
  hT p E (i + j) hij _ fun _ hσ => pair_twist p h hy hz hσ

theorem pair_mem (hA : AxSenTate) [FiniteDimensional ℚ_[p] E]
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {i j : ℤ} (hij : i + j = 0)
    {y z : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i E) (hz : z ∈ Ysp p ρ' j E) :
    ∃ e : E, y ⬝ᵥ z = algebraMap E ℂ_[p] e := by
  obtain ⟨e, he⟩ := hA p E (y ⬝ᵥ z) fun σ hσ => by
    have := pair_twist p h hy hz hσ
    rwa [hij, cycPow_zero, one_smul] at this
  exact ⟨e, by rw [he, eC_eq]⟩

end Pairing

/-! ## §3. The dual basis -/

section DualBasis

variable {K : Type*} [Field K] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector `c_m` with `v ⬝ᵥ c_m = b.coord m v`. -/
def cvec (b : Module.Basis ι K (Fin n → K)) (m : ι) : Fin n → K := fun a => b.coord m (Pi.single a 1)

theorem coord_eq_dot (b : Module.Basis ι K (Fin n → K)) (m : ι) (v : Fin n → K) :
    b.coord m v = v ⬝ᵥ cvec b m := by
  have hv : v = ∑ a, v a • Pi.single a (1 : K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct, cvec]

theorem dot_cvec (b : Module.Basis ι K (Fin n → K)) (k m : ι) :
    b k ⬝ᵥ cvec b m = if k = m then 1 else 0 := by
  rw [← coord_eq_dot, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- A vector is determined by its pairings with a basis. -/
theorem eq_of_dot_basis (b : Module.Basis ι K (Fin n → K)) {x x' : Fin n → K}
    (h : ∀ k, b k ⬝ᵥ x = b k ⬝ᵥ x') : x = x' := by
  have h0 : ∀ v : Fin n → K, v ⬝ᵥ (x - x') = 0 := by
    intro v
    rw [← b.sum_repr v, sum_dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_dotProduct, dotProduct_sub, h k, sub_self, smul_zero]
  ext a
  have := h0 (Pi.single a 1)
  rw [single_dotProduct, one_mul, Pi.sub_apply, sub_eq_zero] at this
  exact this

/-- The dual expansion `z = Σ_m (b_m ⬝ᵥ z) c_m`. -/
theorem dual_expansion (b : Module.Basis ι K (Fin n → K)) (c : ι → Fin n → K)
    (hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0) (z : Fin n → K) :
    z = ∑ m, (b m ⬝ᵥ z) • c m := by
  refine eq_of_dot_basis b fun k => ?_
  rw [dotProduct_sum]
  simp only [dotProduct_smul, hbc, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem linearIndependent_of_dual (b : Module.Basis ι K (Fin n → K)) (c : ι → Fin n → K)
    (hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0) : LinearIndependent K c := by
  rw [Fintype.linearIndependent_iff]
  intro a ha k
  have := congrArg (fun v => b k ⬝ᵥ v) ha
  simp only [dotProduct_sum, dotProduct_smul, hbc, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct_zero] at this
  exact this

end DualBasis

/-! ## §4. Dimensions of the `Y`'s from a dual pair of bases -/

section Dims

variable (p : ℕ) [Fact p.Prime] {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] E]

/-- **Step 3: the dual basis lies in the `Y`'s of the contragredient.** -/
theorem cvec_mem {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p])) (j : ι → ℤ)
    (hb : ∀ k, b k ∈ Ysp p ρ (j k) E) (m : ι) : cvec b m ∈ Ysp p ρ' (-j m) E := by
  intro σ hσ
  rw [h σ]
  -- `ρ(σ) σ(c_m) = χ(σ)^{j_m} c_m`, tested against the basis
  have key : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).mulVec (vAct p σ (cvec b m)) =
      cycPow p σ (j m) • cvec b m := by
    refine eq_of_dot_basis b fun k => ?_
    have h1 : cpAct p σ (b k ⬝ᵥ cvec b m) = (if k = m then 1 else 0) := by
      rw [dot_cvec]; split_ifs <;> simp
    rw [cpAct_dot, vAct_of_mem p (hb k) hσ, smul_dotProduct, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec] at h1
    rw [dotProduct_smul, dot_cvec]
    have h2 : b k ⬝ᵥ (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).mulVec (vAct p σ (cvec b m)) =
        cycPow p σ (j k) • (if k = m then (1 : ℂ_[p]) else 0) := by
      rw [← h1, smul_smul, mul_comm, cycPow_neg_mul, one_smul]
    rw [h2]
    split_ifs with hkm
    · rw [hkm]
    · simp
  have e1 : vAct p σ (cvec b m) = cycPow p σ (j m) •
      (matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)).mulVec (cvec b m) := by
    have h3 := congrArg (matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)).mulVec key
    rw [Matrix.mulVec_mulVec, matC_inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul] at h3
    exact h3
  rw [e1, smul_smul, cycPow_neg_mul, one_smul]

/-- **Step 4: `dim_E Y_i(ρ') = #{m | j_m = −i}`.** -/
theorem finrank_Ysp_dual (hT : TateTwistInvariants) (hA : AxSenTate)
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p])) (j : ι → ℤ) (hb : ∀ k, b k ∈ Ysp p ρ (j k) E)
    (c : ι → Fin n → ℂ_[p]) (hc : ∀ m, c m ∈ Ysp p ρ' (-j m) E)
    (hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0) (i : ℤ) :
    Module.finrank E (Ysp p ρ' i E) = Fintype.card {m // j m = -i} := by
  classical
  let T := {m // j m = -i}
  have hcT : ∀ t : T, c t.1 ∈ Ysp p ρ' i E := fun t => by
    have := hc t.1; rwa [t.2, neg_neg] at this
  let F : (T → E) →ₗ[E] Ysp p ρ' i E :=
    { toFun := fun a => ∑ t, a t • ⟨c t.1, hcT t⟩
      map_add' := fun a a' => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hFval : ∀ a : T → E, ((F a : Ysp p ρ' i E) : Fin n → ℂ_[p]) =
      ∑ t, algebraMap E ℂ_[p] (a t) • c t.1 := by
    intro a
    change ((∑ t, a t • (⟨c t.1, hcT t⟩ : Ysp p ρ' i E) : Ysp p ρ' i E) : Fin n → ℂ_[p]) = _
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Submodule.coe_smul, algebraMap_smul]
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext t
    have h0 : ((F a : Ysp p ρ' i E) : Fin n → ℂ_[p]) = 0 := by rw [ha]; rfl
    rw [hFval] at h0
    have := congrArg (fun v => b t.1 ⬝ᵥ v) h0
    simp only [dotProduct_sum, dotProduct_smul, hbc, smul_eq_mul, mul_ite, mul_one, mul_zero,
      dotProduct_zero] at this
    rw [Finset.sum_eq_single t (fun t' _ ht' => by
      rw [if_neg (fun e => ht' (Subtype.ext e).symm)]) (by simp), if_pos rfl] at this
    rw [Pi.zero_apply]
    exact (algebraMap E ℂ_[p]).injective (this.trans (map_zero _).symm)
  have hsurj : Function.Surjective F := by
    rintro ⟨z, hz⟩
    have hcoef : ∀ m, ∃ e : E, b m ⬝ᵥ z = algebraMap E ℂ_[p] e ∧ (j m ≠ -i → e = 0) := by
      intro m
      by_cases hm : j m + i = 0
      · obtain ⟨e, he⟩ := pair_mem p hA h hm (hb m) hz
        exact ⟨e, he, fun hne => absurd (by omega) hne⟩
      · refine ⟨0, by rw [pair_eq_zero p hT h hm (hb m) hz, map_zero], fun _ => rfl⟩
    choose e he hez using hcoef
    refine ⟨fun t => e t.1, Subtype.ext ?_⟩
    rw [hFval]
    change ∑ t : T, algebraMap E ℂ_[p] (e t.1) • c t.1 = z
    conv_rhs => rw [dual_expansion b c hbc z]
    simp only [he]
    have hR : ∑ m, algebraMap E ℂ_[p] (e m) • c m =
        ∑ m ∈ Finset.univ.filter (fun m => j m = -i), algebraMap E ℂ_[p] (e m) • c m := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs with hm
      · rfl
      · rw [hez m hm, map_zero, zero_smul]
    rw [hR, Finset.sum_subtype (Finset.univ.filter (fun m => j m = -i)) (p := fun m => j m = -i)
      (fun m => by simp)]
  rw [← (LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- **Steps 2-4 together: `dim_E Y_i(ρ') = dim_E Y_{−i}(ρ)` for a dual pair, if `ρ` is Hodge–Tate.** -/
theorem finrank_Ysp_dual_eq (hT : TateTwistInvariants) (hA : AxSenTate)
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') (J : Finset ℤ)
    (hsum : ∑ j ∈ J, Module.finrank E (Ysp p ρ j E) = n) (i : ℤ) :
    Module.finrank E (Ysp p ρ' i E) = Module.finrank E (Ysp p ρ (-i) E) := by
  classical
  obtain ⟨ι, _, b, j, hb⟩ := exists_basis_Ysp p hT hA E ρ J hsum
  let c := cvec b
  have hc : ∀ m, c m ∈ Ysp p ρ' (-j m) E := cvec_mem p h b j hb
  have hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0 := dot_cvec b
  -- `c` is a basis, and `b` is dual to it
  have hcard : Fintype.card ι = Module.finrank ℂ_[p] (Fin n → ℂ_[p]) :=
    (Module.finrank_eq_card_basis b).symm
  let b' : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p]) :=
    basisOfLinearIndependentOfCardEqFinrank' c (linearIndependent_of_dual b c hbc) hcard
  have hb'c : ∀ k, b' k = c k := fun k => by
    simp only [b', coe_basisOfLinearIndependentOfCardEqFinrank']
  have hb' : ∀ k, b' k ∈ Ysp p ρ' ((fun m => -j m) k) E := fun k => by rw [hb'c]; exact hc k
  have hcb : ∀ m, b m ∈ Ysp p ρ (-(fun m => -j m) m) E := fun m => by
    simp only [neg_neg]; exact hb m
  have hb'b : ∀ k m, b' k ⬝ᵥ b m = if k = m then 1 else 0 := fun k m => by
    rw [hb'c, dotProduct_comm, hbc]
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1.symm h2 | exact absurd h2.symm h1
  rw [finrank_Ysp_dual p hT hA h b j hb c hc hbc i,
    finrank_Ysp_dual p hT hA h.symm b' (fun m => -j m) hb' b hcb hb'b (-i)]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun m => ?_)
  constructor <;> intro e <;> omega

end Dims

/-! ## §5. `HTDual` -/

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

theorem dualGR_restrictLocal (ρ : GaloisRep ℓ n) (σ : GQp ℓ) :
    (((dualGR ρ).restrictLocal ℓ σ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) =
      ((ρ.restrictLocal ℓ σ⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).transpose := by
  change (ρ.mat (decomp ℓ σ)⁻¹).transpose = _
  rw [← map_inv]
  rfl

end Main

set_option synthInstance.maxHeartbeats 400000 in
/-- **`HTDual`, proved from Tate's two theorems** (the bundle leaves `tateTwistInvariants`, `axSenTate`). -/
theorem htDual_proof (hT : TateTwistInvariants) (hA : AxSenTate) : HTDual := by
  intro ℓ _ n ρ S hS hρ
  classical
  obtain ⟨E₁, hE₁, ρ₁, h₁, hw₁⟩ := hρ
  let E := IntermediateField.normalClosure ℚ_[ℓ] E₁ (PadicAlgCl ℓ)
  haveI : FiniteDimensional ℚ_[ℓ] E := inferInstance
  haveI : IsGalois ℚ_[ℓ] E := IsGalois.mk
  have hE₁E : E₁ ≤ E := IntermediateField.le_normalClosure E₁
  let ρL := ρ.restrictLocal ℓ
  let ρ'L := (dualGR ρ).restrictLocal ℓ
  have hent₁ : ∀ σ i j, (((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j : E₁) : PadicAlgCl ℓ) =
      (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j := by
    intro σ i j; rw [← h₁ σ]; rfl
  have hmem : ∀ σ i j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j ∈ E := by
    intro σ i j; rw [← hent₁]
    exact hE₁E ((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j).2
  have hmem' : ∀ σ i j, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j ∈ E := by
    intro σ i j
    rw [dualGR_restrictLocal ρ σ, Matrix.transpose_apply]
    exact hmem σ⁻¹ j i
  let ρE := liftGL E ρL hmem
  let ρ'E := liftGL E ρ'L hmem'
  have hwE : ∀ w, htMult ℓ ρE w = S.count w := fun w =>
    (htMult_eq_of_lifts ℓ ρL ρE ρ₁ (liftGL_map E ρL hmem) h₁ w).trans (hw₁ w)
  have hdual : IsDualPair ℓ ρE ρ'E := by
    intro σ
    ext a b
    simp only [matC, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
    apply Subtype.ext
    rw [liftGL_coe, liftGL_coe, dualGR_restrictLocal ρ σ, Matrix.transpose_apply]
  have hdY : ∀ i, Module.finrank E (Ysp ℓ ρE i E) = S.count (-i) := by
    intro i; rw [← hwE, htMult_eq_finrank_Ysp ℓ hT hA E ρE (-i), neg_neg]
  let J : Finset ℤ := (S.map fun w => -w).toFinset
  have hsum : ∑ j ∈ J, Module.finrank E (Ysp ℓ ρE j E) = n := by
    simp only [hdY]
    have hJ : J = S.toFinset.map ⟨fun w => -w, neg_injective⟩ := by
      ext j; simp [J]
    rw [hJ, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, neg_neg]
    rw [Multiset.toFinset_sum_count_eq, hS]
  refine ⟨E, inferInstance, ρ'E, liftGL_map E ρ'L hmem', fun w => ?_⟩
  rw [htMult_eq_finrank_Ysp ℓ hT hA E ρ'E w, finrank_Ysp_dual_eq ℓ hT hA hdual J hsum, neg_neg, hdY]
  have := Multiset.count_map_eq_count' (fun w : ℤ => -w) S neg_injective (-w)
  simp only [neg_neg] at this
  exact this.symm

end

end EigenformHTExists

/-! ## §6. The contragredient of a semisimple representation is semisimple (c-to-printed2, verbatim) -/

namespace EigenformHTExists

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

section DualSS

variable {K : Type*} [Field K] {n : ℕ}

/-- `v ↦ (w ↦ w ⬝ᵥ v)`, i.e. `(Pi.basisFun K (Fin n)).toDualEquiv`. -/
theorem toDual_eq_dot (v w : Fin n → K) : (Pi.basisFun K (Fin n)).toDual v w = w ⬝ᵥ v := by
  have hw : w = ∑ i, w i • Pi.basisFun K (Fin n) i := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]

/-- The orthogonal of `W` for the dot product. -/
def perp (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  W.dualAnnihilator.comap ((Pi.basisFun K (Fin n)).toDualEquiv : (Fin n → K) →ₗ[K] Module.Dual K (Fin n → K))

theorem mem_perp (W : Submodule K (Fin n → K)) (v : Fin n → K) : v ∈ perp W ↔ ∀ w ∈ W, w ⬝ᵥ v = 0 := by
  simp only [perp, Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearEquiv.coe_coe,
    Module.Basis.toDualEquiv_apply, toDual_eq_dot]

theorem finrank_perp (W : Submodule K (Fin n → K)) : Module.finrank K (perp W) = n - Module.finrank K W := by
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have h2 : Module.finrank K (perp W) = Module.finrank K W.dualAnnihilator := by
    rw [perp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  rw [Module.finrank_fin_fun] at h1
  omega

theorem eq_zero_of_dot (w : Fin n → K) (h : ∀ v, w ⬝ᵥ v = 0) : w = 0 := by
  ext i
  have := h (Pi.single i 1)
  rwa [dotProduct_single, mul_one] at this

end DualSS

section DualSSRep

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

theorem mulVec_mem_of_stable {M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)}
    {W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)} (h : W.map (Matrix.toLin' M) ≤ W)
    {w : Fin n → PadicAlgCl ℓ} (hw : w ∈ W) : M.mulVec w ∈ W := by
  have := h (Submodule.mem_map_of_mem (f := Matrix.toLin' M) hw)
  rwa [Matrix.toLin'_apply] at this

/-- **The contragredient of a semisimple representation is semisimple.** -/
theorem dualGR_isSemisimple (ρ : GaloisRep ℓ n) (h : ρ.IsSemisimple) : (dualGR ρ).IsSemisimple := by
  intro W hW
  -- `W^⊥` is `ρ`-stable
  have hP : ∀ σ, (perp W).map (Matrix.toLin' (ρ.mat σ)) ≤ perp W := by
    rintro σ _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply, mem_perp]
    intro w hw
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have : (ρ.mat σ).transpose = (dualGR ρ).mat σ⁻¹ := by rw [dualGR_mat, inv_inv]
    rw [this]
    exact (mem_perp W v).1 hv _ (mulVec_mem_of_stable (hW σ⁻¹) hw)
  obtain ⟨U, hcompl, hU⟩ := h (perp W) hP
  refine ⟨perp U, ?_, ?_⟩
  · rw [Submodule.isCompl_iff_disjoint]
    · rw [Submodule.disjoint_def]
      intro w hw hwU
      refine eq_zero_of_dot w fun v => ?_
      have hv : v ∈ perp W ⊔ U := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hv
      rw [dotProduct_add, (mem_perp W a).1 ha w hw, dotProduct_comm, (mem_perp U w).1 hwU u hu, zero_add]
    · have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
      have h2 := finrank_perp W
      have h3 := finrank_perp U
      have hWle : Module.finrank (PadicAlgCl ℓ) W ≤ n := by
        have := Submodule.finrank_le W; rwa [Module.finrank_fin_fun] at this
      rw [Module.finrank_fin_fun] at h1 ⊢
      omega
  · rintro σ _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply, mem_perp]
    intro u hu
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dualGR_mat, Matrix.transpose_transpose]
    exact (mem_perp U v).1 hv _ (mulVec_mem_of_stable (hU σ⁻¹) hu)

end DualSSRep

/-! ## §7. The new leaf (existence form) and the discharge -/

/-- **New leaf (R13, existence form): Kato's theorem for newforms, at the representation the source builds.**
For a newform `f ∈ S_k(Γ₁(N))` of weight `k ≥ 2`, level `N ≥ 1` and nebentypus `χ`, a prime `ℓ` and embeddings
`ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`, **there is** a semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` that is unramified
at every prime `p ∤ Nℓ`, where every **geometric** Frobenius `σ⁻¹` (`σ` an arithmetic Frobenius at a place over
`p`) has trace `ιL ιC⁻¹ a_p(f)`, and whose restriction to `G_{ℚ_ℓ}` is Hodge–Tate with weights `{0, k − 1}`
(the kernel's convention: the cyclotomic character has weight `−1`, so `H¹` of an elliptic curve has `{0, 1}`).

Witness: `V_{F_λ}(f) ⊗_{F_λ, ιL ιC⁻¹} ℚ̄_ℓ`, Kato's Hecke quotient of the étale cohomology of the modular curve
with coefficients `Sym^{k−2}` (Deligne's construction).
Sources: Kato, *p-adic Hodge theory and values of zeta functions of modular forms*, Astérisque 295 (2004):
§§9.2-9.4, (9.2.2), pp. 187-188 (de Rham at `ℓ`, every level, `ℓ ∣ N` included) and §11.3, pp. 205-207 (the Hodge
filtration of `D_dR(V_{F_λ}(f))`, jumps `0` and `k − 1`); §6.3 and §8.3, pp. 161-162 and 181-182 (definition and
Frobenius normalization of `V_{F_λ}(f)`) (pages read by the locator audit, row R13; the wording is UNVERIFIED).
Alternatives: Faltings, Math. Ann. 278 (1987) and Scholl, Invent. Math. 100 (1990) (Hodge–Tate / de Rham for
`ℓ ∤ N`), Saito, Invent. Math. 129 (1997) (all levels; UNVERIFIED). Semisimplicity: Ribet 1977 (`k = 2`) and
Ribet 1985 (irreducibility; UNVERIFIED locators). Not stronger than the print: it asserts the conclusion for one
representation (`∃`), with semisimplicity in place of the printed irreducibility. Kind: published, pending reading
(see the report for the points a reading must settle: Frobenius normalization `a_p` vs `ā_p`, sign convention of
the weights). Same statement as c-to-printed2's `KatoRealizationCohSS`. -/
def KatoHTExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, k - 1}

/-- **Duality step** (GLUE, proved): the contragredient of a cohomologically normalized witness is semisimple,
attached to `f` in the trace form `AttachedTo`, and has Hodge–Tate weights `{0, 1 − k}`. -/
theorem dual_of_coh {ℓ : ℕ} [Fact ℓ.Prime] (hD : HTDual) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (f : CF N k) (ρ : GaloisRep ℓ 2)
    (hss : ρ.IsSemisimple)
    (hatt : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α)
    (hHT : ρ.HasHTWeightsAtSelf ℓ {0, k - 1}) :
    (dualGR ρ).IsSemisimple ∧ (dualGR ρ).AttachedTo ιC ιL f ∧
      (dualGR ρ).HasHTWeightsAtSelf ℓ {0, 1 - k} := by
  refine ⟨dualGR_isSemisimple ρ hss, ?_, ?_⟩
  · intro p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    refine ⟨fun v hv σ hσ => ?_, α, hα, fun v σ hv hσ => ?_⟩
    · have h1 := hu v hv σ⁻¹ ((v.inertiaSubgroup ℚ).inv_mem hσ)
      apply Units.ext
      change (ρ.mat ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹).transpose = 1
      have : ((σ⁻¹ : v.decompositionSubgroup ℚ) : GQ) = ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹ := rfl
      rw [GaloisRep.mat, ← this, h1, Units.val_one, Matrix.transpose_one]
    · rw [dualGR_mat, Matrix.trace_transpose, htr v σ hv hσ]
  · have h := hD ℓ 2 ρ {0, k - 1} (by simp) hHT
    have hS : (({0, k - 1} : Multiset ℤ).map Neg.neg) = {0, 1 - k} := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]
    rwa [hS] at h

/-- **Transport step** (GLUE, proved: Chebotarev + Brauer–Nesbitt `attachedConj_proof`, invariance of Hodge–Tate
weights under conjugation `htConj_proof`): if one semisimple `ρ₀` attached to `f` has Hodge–Tate weights `S`,
so does every semisimple `ρ` attached to `f`. -/
theorem ht_of_attached {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} (hN : 0 < N) {k : ℤ} (f : CF N k) (ρ₀ ρ : GaloisRep ℓ 2) (S : Multiset ℤ)
    (hss₀ : ρ₀.IsSemisimple) (hatt₀ : ρ₀.AttachedTo ιC ιL f) (hHT₀ : ρ₀.HasHTWeightsAtSelf ℓ S)
    (hss : ρ.IsSemisimple) (hatt : ρ.AttachedTo ιC ιL f) : ρ.HasHTWeightsAtSelf ℓ S := by
  have hconj : IsConj ρ₀ ρ := by
    refine attachedConj_proof ℓ ρ₀ ρ (N * ℓ).primeFactors hss₀ hss fun p hp hpS => ?_
    have hpN : ¬ p ∣ N * ℓ := by
      intro h
      exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h, Nat.mul_ne_zero (by omega)
        (Fact.out : ℓ.Prime).ne_zero⟩)
    obtain ⟨hu₀, α₀, hα₀, htr₀⟩ := hatt₀ p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    have heq : α₀ = α := by
      apply ιC.toRingHom.injective
      change ιC α₀ = ιC α
      rw [hα₀, hα]
    refine ⟨hu₀, hu, fun v σ hv hσ => ?_⟩
    rw [htr₀ v σ hv hσ, htr v σ hv hσ, heq]
  exact htConj_proof ℓ 2 ρ₀ ρ S hconj hHT₀

/-- **The field `eigenformHTNew` from the existence form** (GLUE, proved; uses the bundle LEAF fields
`tateTwistInvariants`, `axSenTate` for the duality step). -/
theorem eigenformHTNew_of_katoHTExists (hK : KatoHTExists) (hT : TateTwistInvariants) (hA : AxSenTate) :
    EigenformHTNew := by
  intro ℓ _ ιC ιL N k χ f ρ hN hk hf hss hatt
  obtain ⟨ρ₀, hss₀, hatt₀, hHT₀⟩ := hK ℓ ιC ιL N k χ f hN hk hf
  obtain ⟨hss₀', hatt₀', hHT₀'⟩ := dual_of_coh (htDual_proof hT hA) ιC ιL f ρ₀ hss₀ hatt₀ hHT₀
  exact ht_of_attached ιC ιL hN f (dualGR ρ₀) ρ _ hss₀' hatt₀' hHT₀' hss hatt

/-- **Duality step, converse direction** (GLUE, proved): the contragredient of a semisimple `ρ` attached to `f`
in the trace form is cohomologically normalized, with Hodge–Tate weights `{0, k − 1}`. -/
theorem coh_of_dual {ℓ : ℕ} [Fact ℓ.Prime] (hD : HTDual) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (f : CF N k) (ρ : GaloisRep ℓ 2)
    (hss : ρ.IsSemisimple) (hatt : ρ.AttachedTo ιC ιL f) (hHT : ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}) :
    (dualGR ρ).IsSemisimple ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → (dualGR ρ).UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          ((dualGR ρ).mat σ⁻¹).trace = ιL α) ∧
      (dualGR ρ).HasHTWeightsAtSelf ℓ {0, k - 1} := by
  refine ⟨dualGR_isSemisimple ρ hss, ?_, ?_⟩
  · intro p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    refine ⟨fun v hv σ hσ => ?_, α, hα, fun v σ hv hσ => ?_⟩
    · have h1 := hu v hv σ⁻¹ ((v.inertiaSubgroup ℚ).inv_mem hσ)
      apply Units.ext
      change (ρ.mat ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹).transpose = 1
      have : ((σ⁻¹ : v.decompositionSubgroup ℚ) : GQ) = ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹ := rfl
      rw [GaloisRep.mat, ← this, h1, Units.val_one, Matrix.transpose_one]
    · rw [dualGR_mat, inv_inv, Matrix.trace_transpose, htr v σ hv hσ]
  · have h2 := hD ℓ 2 ρ {0, 1 - k} (by simp) hHT
    have hS : (({0, 1 - k} : Multiset ℤ).map Neg.neg) = {0, k - 1} := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]
    rwa [hS] at h2

/-- **Converse: the field gives back the leaf** over the bundle LEAF fields `dsThm965`, `dsThm966` (existence of
a semisimple attached `ρ`, through `r14Det_of_printed`) and `tateTwistInvariants`, `axSenTate` (duality). So
the new leaf is no stronger than the field it replaces. -/
theorem katoHTExists_of_eigenformHTNew (hD : DSThm965) (hDS : DSThm966) (hT : TateTwistInvariants)
    (hA : AxSenTate) (h : EigenformHTNew) : KatoHTExists := by
  intro ℓ _ ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hss, hatt⟩ :=
    eigenformRepExists_of_r14Det (r14Det_of_printed hD hDS) ℓ ιC ιL N k χ f hN (by omega) hf.1
  exact ⟨dualGR ρ, coh_of_dual (htDual_proof hT hA) ιC ιL f ρ hss hatt
    (h ℓ ιC ιL N k χ f ρ hN hk hf hss hatt)⟩

theorem katoHTExists_iff (hD : DSThm965) (hDS : DSThm966) (hT : TateTwistInvariants) (hA : AxSenTate) :
    KatoHTExists ↔ EigenformHTNew :=
  ⟨fun hK => eigenformHTNew_of_katoHTExists hK hT hA, katoHTExists_of_eigenformHTNew hD hDS hT hA⟩

/-! ## §8. The instance the route uses: `ℓ = 5`, `k ≥ 3` (ht-bypass) -/

/-- **`KatoHTExists` at `ℓ = 5` and weight `k ≥ 3`** (the only instance the route uses, ht-bypass): Kato's
theorem for newforms of weight `≥ 3` at `ℓ = 5`, every level (including `5 ∣ N`), existence form, cohomological
normalization. Same sources as `KatoHTExists`; a special case of it (`katoHTExists5Ge3_of_katoHTExists`). -/
def KatoHTExists5Ge3 : Prop :=
  ∀ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 3 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep 5 2, ρ.IsSemisimple ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * 5 → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf 5 {0, k - 1}

theorem katoHTExists5Ge3_of_katoHTExists (h : KatoHTExists) : KatoHTExists5Ge3 :=
  fun ιC ιL N k χ f hN hk hf => h 5 ιC ιL N k χ f hN (by omega) hf

/-- **ht-bypass's weakest form `EigenformHTNew5Ge3` from the restricted existence form** (GLUE, proved). -/
theorem eigenformHTNew5Ge3_of_katoHTExists5Ge3 (hK : KatoHTExists5Ge3) (hT : TateTwistInvariants)
    (hA : AxSenTate) : ZInQ.Contrib.HodgeSplit.HTBypass.EigenformHTNew5Ge3 := by
  intro ιC ιL N k χ f ρ hN hk hf hss hatt
  obtain ⟨ρ₀, hss₀, hatt₀, hHT₀⟩ := hK ιC ιL N k χ f hN hk hf
  obtain ⟨hss₀', hatt₀', hHT₀'⟩ := dual_of_coh (htDual_proof hT hA) ιC ιL f ρ₀ hss₀ hatt₀ hHT₀
  exact ht_of_attached ιC ιL hN f (dualGR ρ₀) ρ _ hss₀' hatt₀' hHT₀' hss hatt

/-- Converse of the restricted form (as `katoHTExists_of_eigenformHTNew`). -/
theorem katoHTExists5Ge3_of_eigenformHTNew5Ge3 (hD : DSThm965) (hDS : DSThm966) (hT : TateTwistInvariants)
    (hA : AxSenTate) (h : ZInQ.Contrib.HodgeSplit.HTBypass.EigenformHTNew5Ge3) : KatoHTExists5Ge3 := by
  intro ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hss, hatt⟩ :=
    eigenformRepExists_of_r14Det (r14Det_of_printed hD hDS) 5 ιC ιL N k χ f hN (by omega) hf.1
  exact ⟨dualGR ρ, coh_of_dual (htDual_proof hT hA) ιC ιL f ρ hss hatt
    (h ιC ιL N k χ f ρ hN hk hf hss hatt)⟩

/-- **The consumer input** `G0Galois.EigenformHT5Ge3Chain` (the argument `r13w` of ht-bypass's `afterG7_of3Weak`)
from the restricted leaf and the bundle LEAF fields `tateTwistInvariants`, `axSenTate`, `dsThm965`, `dsThm966`. -/
theorem eigenformHT5Ge3Chain_of_katoHTExists5Ge3 (hK : KatoHTExists5Ge3) (hT : TateTwistInvariants)
    (hA : AxSenTate) (hD : DSThm965) (hDS : DSThm966) : HDec.G0Galois.EigenformHT5Ge3Chain :=
  HDec.G0Galois.eigenformHT5Ge3Chain_of
    (ZInQ.Contrib.HodgeSplit.HTBypass.eigenformHT5Ge3_of_ds
      (eigenformHTNew5Ge3_of_katoHTExists5Ge3 hK hT hA) hD hDS)

end

end EigenformHTExists

/-! ## §9. The consumer chain with the restricted leaf

ht-bypass's `afterG7_of3Weak` (`AfterG7`, the input of `GluePieces.modularConstituent`) with its argument `r13w`
supplied by the restricted leaf `KatoHTExists5Ge3` and the bundle LEAF fields `tateTwistInvariants`, `axSenTate`,
`dsThm965`, `dsThm966`. For a later bypass fold; the autofold discharge above does not need it. -/

namespace HDec

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open _root_.HDec.G0ModField

/-- **`AfterG7` from the restricted existence form** (`afterG7_of3Weak` with
`eigenformHT5Ge3Chain_of_katoHTExists5Ge3`). -/
theorem afterG7_of3Kato5 (r9a : PkgI3.FaltingsSemisimple) (r9b : PkgI3.FaltingsTate)
    (r10 : PkgI4.DeRhamComparison) (r11r12 : PkgI4.PanBerger) (r14 : EigenformRepExists)
    (hK5 : _root_.EigenformHTExists.KatoHTExists5Ge3)
    (hT : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants) (hA : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate)
    (hD : _root_.ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : _root_.ZInQ.Contrib.HodgeSplit.DSThm966)
    (r15 : DeligneSerreConseq)
    (r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1')
    (t : TextbookLeaves) (m : G0Galois.GaloisPieces) (hWw : G0Galois.G12WeightWeak)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 :=
  afterG7_of3Weak r9a r9b r10 r11r12 r14
    (_root_.EigenformHTExists.eigenformHT5Ge3Chain_of_katoHTExists5Ge3 hK5 hT hA hD hDS) r15 r16 t m hWw h9 hDF
    hCar hSw hL8 hAd hG36 hLink

end HSyn.G0AssembleMod

end HDec
