import ZInQKernel.Contrib.OneProof.NewformDict
import ZInQKernel.Contrib.OneProof.DSCoeffExt
import ZInQKernel.Contrib.OneProof.TateTwistInvariants
import ZInQKernel.Contrib.OneProof.AxSenTate

/-! # htnew-print: `eigenformHTNew` from the printed existence theorem, robust to every reading

Task htnew-print, 2026-11-17 (report `docs/research/htnew-print.md`, log `scratch/htnew-print/log.md`).

The open field `eigenformHTNew : ZInQ.Contrib.HodgeSplit.EigenformHTNew` says: **every** semisimple
`ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to a newform `f` of weight `k ≥ 2` (trace form `AttachedTo`: arithmetic
Frobenius, trace `a_p`) has Hodge–Tate weights `{0, 1 − k}` at `ℓ`. ht-exists reduced it to an existence-form
leaf flagged *pending reading* on three points: the sign convention of the weights / the Frobenius
normalization, and the semisimplicity of the witness. This file states the existence theorem so that **every
reading of every printed wording** gives it (`ModularHTPrinted`, §7), and proves the field from it:

* the witness may be normalized either way (arithmetic Frobenius with weights `{0, 1 − k}`, or geometric
  Frobenius with weights `{0, k − 1}`, in the kernel's convention where the cyclotomic character has weight `−1`);
  the disjunction is the or-introduction of whichever the print says (the two combinations are the only true
  ones; translating the print's convention to the kernel's `htMult` lands in one of them);
* no semisimplicity is asked of the witness: §6 proves in Lean that the semisimplification of a `2`-dimensional
  Hodge–Tate representation is Hodge–Tate with the same weights (triangularize, compare Tate–Sen spaces `Y_i`);
* the Frobenius clause is the trace, which the "characteristic polynomial" wording gives (`trace_of_charpoly`);
* the newform is Tau Ceti's printed `Newform N k` (newform-dict: `NewformDict.g9_isNewform_iff`).

§1-§5 (the contragredient and `HTDual`) are ht-exists's file verbatim, namespace renamed. Tate's two theorems,
inputs of `HTDual` and of §6, are proved on main (`ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof`,
`axSenTate_proof`).

No `sorry`, no `axiom`, no code that runs at build time.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace EigenformHTPrinted

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

end EigenformHTPrinted

/-! ## §6. Semisimplification preserves Hodge–Tate weights (dimension `2`) -/

namespace EigenformHTPrinted

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

/-- Tate 1967 §3.3 Thm 2 (twist invariants), proved on main. -/
theorem tate : TateTwistInvariants := ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof

/-- Tate 1967 §3.3 Thm 1 (Ax–Sen–Tate), proved on main. -/
theorem axSen : AxSenTate := ZInQ.Contrib.CloudB3W11.axSenTate_proof

/-- `HTDual`, unconditional. -/
theorem htDual : HTDual := htDual_proof tate axSen

section LinAlg

variable {K : Type*} [Field K]

/-- A subspace of `K²` other than `0` and `K²` is a line `K w`. -/
theorem exists_gen_of_ne {W : Submodule K (Fin 2 → K)} (h0 : W ≠ ⊥) (h2 : W ≠ ⊤) :
    ∃ w : Fin 2 → K, w ≠ 0 ∧ finrank K W = 1 ∧ ∀ x, x ∈ W ↔ ∃ c : K, x = c • w := by
  have hle : finrank K W ≤ 2 := by
    have := Submodule.finrank_le W
    rwa [Module.finrank_fin_fun] at this
  have hne0 : finrank K W ≠ 0 := fun h => h0 (Submodule.finrank_eq_zero.mp h)
  have hne2 : finrank K W ≠ 2 := by
    intro h
    exact h2 (Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun]))
  have h1 : finrank K W = 1 := by omega
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp h1
  refine ⟨v, fun h => hv (Subtype.ext h), h1, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := hspan ⟨x, hx⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨c, rfl⟩
    exact W.smul_mem c v.2

theorem single_ne_zero (i : Fin 2) : (Pi.single i (1 : K) : Fin 2 → K) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

/-- A line `K w` with `w_j ≠ 0` is complementary to the coordinate line `K e_i`, `i ≠ j`. -/
theorem isCompl_line {W : Submodule K (Fin 2 → K)} {w : Fin 2 → K} (h1 : finrank K W = 1)
    (hW : ∀ x, x ∈ W ↔ ∃ c : K, x = c • w) {i j : Fin 2} (hij : i ≠ j) (hj : w j ≠ 0) :
    IsCompl W (K ∙ (Pi.single i (1 : K) : Fin 2 → K)) := by
  rw [Submodule.isCompl_iff_disjoint]
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := (hW x).1 hx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx'
    have hc : c = 0 := by
      have := congrFun hb j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, if_neg (Ne.symm hij), mul_zero] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact h
      · exact absurd h hj
    rw [hc, zero_smul]
  · rw [h1, finrank_span_singleton (single_ne_zero i), Module.finrank_fin_fun]

/-- A coordinate line is stable under a diagonal matrix. -/
theorem line_stable (M : Matrix (Fin 2) (Fin 2) K) (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) (i : Fin 2) :
    (K ∙ (Pi.single i (1 : K) : Fin 2 → K)).map (Matrix.toLin' M) ≤ K ∙ (Pi.single i (1 : K)) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  refine Submodule.mem_span_singleton.2 ⟨a * M i i, ?_⟩
  rw [Matrix.toLin'_apply, Matrix.mulVec_smul, Matrix.mulVec_single_one, mul_smul]
  congr 1
  funext m
  fin_cases i <;> fin_cases m <;> simp [Matrix.col_apply, h01, h10]

end LinAlg

section Global

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem mulVec_mem_of_stable {n : ℕ} {M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)}
    {W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)} (h : W.map (Matrix.toLin' M) ≤ W)
    {w : Fin n → PadicAlgCl ℓ} (hw : w ∈ W) : M.mulVec w ∈ W := by
  have := h (Submodule.mem_map_of_mem (f := Matrix.toLin' M) hw)
  rwa [Matrix.toLin'_apply] at this

/-- **Diagonal representations are semisimple.** -/
theorem isSemisimple_of_diag (ρ : GaloisRep ℓ 2) (h01 : ∀ σ, ρ.mat σ 0 1 = 0)
    (h10 : ∀ σ, ρ.mat σ 1 0 = 0) : ρ.IsSemisimple := by
  intro W _
  by_cases h0 : W = ⊥
  · exact ⟨⊤, h0 ▸ isCompl_bot_top, fun _ => le_top⟩
  by_cases h2 : W = ⊤
  · exact ⟨⊥, h2 ▸ isCompl_top_bot, fun _ => by rw [Submodule.map_bot]⟩
  obtain ⟨w, hw0, hW1, hmem⟩ := exists_gen_of_ne h0 h2
  by_cases hw : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro h; apply hw0; funext m; fin_cases m
      · exact hw
      · exact h
    exact ⟨_, isCompl_line hW1 hmem (i := 0) (j := 1) (by decide) hw1,
      fun σ => line_stable _ (h01 σ) (h10 σ) 0⟩
  · exact ⟨_, isCompl_line hW1 hmem (i := 1) (j := 0) (by decide) hw,
      fun σ => line_stable _ (h01 σ) (h10 σ) 1⟩

/-- A non-semisimple `2`-dimensional representation has an invariant line. -/
theorem exists_invariant_line (ρ : GaloisRep ℓ 2) (h : ¬ ρ.IsSemisimple) :
    ∃ w : Fin 2 → PadicAlgCl ℓ, w ≠ 0 ∧ ∀ σ, ∃ c : PadicAlgCl ℓ, (ρ.mat σ).mulVec w = c • w := by
  unfold GaloisRep.IsSemisimple at h
  push_neg at h
  obtain ⟨W, hW, hno⟩ := h
  have h0 : W ≠ ⊥ := by
    rintro rfl
    obtain ⟨σ, hσ⟩ := hno ⊤ isCompl_bot_top
    exact hσ le_top
  have h2 : W ≠ ⊤ := by
    rintro rfl
    obtain ⟨σ, hσ⟩ := hno ⊥ isCompl_top_bot
    exact hσ (by rw [Submodule.map_bot])
  obtain ⟨w, hw0, _, hmem⟩ := exists_gen_of_ne h0 h2
  refine ⟨w, hw0, fun σ => (hmem _).1 ?_⟩
  exact mulVec_mem_of_stable (hW σ) ((hmem w).2 ⟨1, (one_smul _ _).symm⟩)

/-- An invertible matrix with first column `w ≠ 0`. -/
theorem exists_gl_col (w : Fin 2 → PadicAlgCl ℓ) (hw : w ≠ 0) :
    ∃ P : GL (Fin 2) (PadicAlgCl ℓ),
      (P : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (Pi.single 0 1) = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h; apply hw; funext m; fin_cases m
      · exact h0
      · exact h
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; w 1, 0] (by
      rw [Matrix.det_fin_two_of]; simpa using h1), ?_⟩
    funext m
    fin_cases m <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, h0]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![w 0, 0; w 1, 1] (by
      rw [Matrix.det_fin_two_of]; simpa using h0), ?_⟩
    funext m
    fin_cases m <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- `P⁻¹ ρ P`. -/
def conjGR {n : ℕ} (ρ : GaloisRep ℓ n) (P : GL (Fin n) (PadicAlgCl ℓ)) : GaloisRep ℓ n where
  toHom := (MulAut.conj P⁻¹).toMonoidHom.comp ρ.toHom
  continuous_toHom := by
    change Continuous fun σ => P⁻¹ * ρ.toHom σ * P⁻¹⁻¹
    exact (continuous_const.mul ρ.continuous_toHom).mul continuous_const

theorem conjGR_toHom {n : ℕ} (ρ : GaloisRep ℓ n) (P : GL (Fin n) (PadicAlgCl ℓ)) (σ : GQ) :
    (conjGR ρ P).toHom σ = P⁻¹ * ρ.toHom σ * P := by
  change P⁻¹ * ρ.toHom σ * P⁻¹⁻¹ = _
  rw [inv_inv]

theorem isConj_conjGR {n : ℕ} (ρ : GaloisRep ℓ n) (P : GL (Fin n) (PadicAlgCl ℓ)) :
    IsConj ρ (conjGR ρ P) :=
  ⟨P, fun σ => by rw [conjGR_toHom]; group⟩

theorem conjGR_mat {n : ℕ} (ρ : GaloisRep ℓ n) (P : GL (Fin n) (PadicAlgCl ℓ)) (σ : GQ) :
    (conjGR ρ P).mat σ = (P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) * ρ.mat σ * P := by
  rw [GaloisRep.mat, conjGR_toHom, Units.val_mul, Units.val_mul]
  rfl

/-- A `GaloisRep` from a continuous multiplicative matrix-valued map. -/
def ofMat {n : ℕ} (D : GQ → Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))
    (hmul : ∀ g h, D (g * h) = D g * D h) (hone : D 1 = 1) (hc : Continuous D) : GaloisRep ℓ n where
  toHom :=
    { toFun := fun g => ⟨D g, D g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
        by rw [← hmul, inv_mul_cancel, hone]⟩
      map_one' := Units.ext hone
      map_mul' := fun g h => Units.ext (hmul g h) }
  continuous_toHom := by
    rw [Units.continuous_iff]
    exact ⟨hc, hc.comp continuous_inv⟩

theorem ofMat_mat {n : ℕ} (D : GQ → Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))
    (hmul : ∀ g h, D (g * h) = D g * D h) (hone : D 1 = 1) (hc : Continuous D) (σ : GQ) :
    (ofMat D hmul hone hc).mat σ = D σ := rfl

/-- The diagonal part of an upper triangular representation. -/
def diagGR (ρ : GaloisRep ℓ 2) (h10 : ∀ σ, ρ.mat σ 1 0 = 0) : GaloisRep ℓ 2 :=
  ofMat (fun σ => !![ρ.mat σ 0 0, 0; 0, ρ.mat σ 1 1])
    (fun g h => by
      have e : ρ.mat (g * h) = ρ.mat g * ρ.mat h := by
        rw [GaloisRep.mat, GaloisRep.mat, GaloisRep.mat, map_mul, Units.val_mul]
      rw [e, Matrix.mul_fin_two]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, mul_zero, zero_mul, add_zero, zero_add])
    (by
      have e : ρ.mat 1 = 1 := by rw [GaloisRep.mat, map_one, Units.val_one]
      rw [e]
      ext i j
      fin_cases i <;> fin_cases j <;> simp)
    (by
      have hc : ∀ i j : Fin 2, Continuous fun σ => ρ.mat σ i j := fun i j =>
        (Units.continuous_val.comp ρ.continuous_toHom).matrix_elem i j
      refine continuous_pi fun i => continuous_pi fun j => ?_
      fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
        Matrix.head_fin_const, Fin.zero_eta, Fin.mk_one, Fin.isValue]
      · exact hc 0 0
      · exact continuous_const
      · exact continuous_const
      · exact hc 1 1)

theorem diagGR_mat (ρ : GaloisRep ℓ 2) (h10 : ∀ σ, ρ.mat σ 1 0 = 0) (σ : GQ) :
    (diagGR ρ h10).mat σ = !![ρ.mat σ 0 0, 0; 0, ρ.mat σ 1 1] := rfl

end Global

end

end EigenformHTPrinted

/-! ## §6b. The Tate–Sen spaces of a triangular representation and of its diagonal -/

namespace EigenformHTPrinted

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

section LocalSS

variable (p : ℕ) [Fact p.Prime]

/-- **The Tate–Sen bound** `Σ_{j ∈ J} dim_K Y_j(ρ) ≤ n` (from (T) `Ysp_linearIndependent`). -/
theorem sum_finrank_Ysp_le (hT : TateTwistInvariants) (hA : AxSenTate) {n : ℕ}
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E) (J : Finset ℤ) :
    ∑ j ∈ J, finrank K (Ysp p ρ j K) ≤ n := by
  classical
  haveI : ∀ j : ℤ, FiniteDimensional K (Ysp p ρ j K) := fun j => Ysp_finiteDimensional p hT hA K ρ j
  haveI : ∀ j : ℤ, Module.Free K (Ysp p ρ j K) := fun j => Module.Free.of_divisionRing _ _
  let d : J → ℕ := fun jj => finrank K (Ysp p ρ jj K)
  let bv : (Σ jj : J, Fin (d jj)) → (Fin n → ℂ_[p]) := fun k =>
    ((Module.finBasis K (Ysp p ρ k.1 K) k.2 : Ysp p ρ k.1 K) : Fin n → ℂ_[p])
  let jf : (Σ jj : J, Fin (d jj)) → ℤ := fun k => k.1
  have hli : LinearIndependent ℂ_[p] bv := by
    refine Ysp_linearIndependent p hT hA K ρ jf bv (fun k => (Module.finBasis K _ k.2).2) ?_
    intro j₀ a ha hs
    by_cases hj₀ : j₀ ∈ J
    · let jj₀ : J := ⟨j₀, hj₀⟩
      have h1 : ∑ m : Fin (d jj₀), a ⟨jj₀, m⟩ • (Module.finBasis K (Ysp p ρ jj₀ K) m) = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero]
        simp only [Submodule.coe_smul]
        rw [← hs, Fintype.sum_sigma, Finset.sum_eq_single jj₀]
        · intro jj _ hjj
          refine Finset.sum_eq_zero fun m _ => ?_
          rw [ha ⟨jj, m⟩ (fun h => hjj (Subtype.ext h)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h2 := Fintype.linearIndependent_iff.mp (Module.finBasis K (Ysp p ρ jj₀ K)).linearIndependent _ h1
      intro k
      by_cases hk : (k.1 : ℤ) = j₀
      · obtain ⟨jj, m⟩ := k
        have : jj = jj₀ := Subtype.ext hk
        subst this
        exact h2 m
      · exact ha k hk
    · intro k
      exact ha k (fun h => hj₀ (h ▸ k.1.2))
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_sigma, Module.finrank_fin_fun] at hcard
  simp only [Fintype.card_fin, d] at hcard
  rwa [Finset.sum_coe_sort J (fun j => finrank K (Ysp p ρ j K))] at hcard

theorem transpose_mulVec_zero (M : Matrix (Fin 2) (Fin 2) ℂ_[p]) (y : Fin 2 → ℂ_[p]) :
    (M.transpose.mulVec y) 0 = M 0 0 * y 0 + M 1 0 * y 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]

theorem transpose_mulVec_one (M : Matrix (Fin 2) (Fin 2) ℂ_[p]) (y : Fin 2 → ℂ_[p]) :
    (M.transpose.mulVec y) 1 = M 0 1 * y 0 + M 1 1 * y 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]

variable {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- Membership in `Y_i` in coordinates (dimension `2`). -/
theorem mem_Ysp_two (ρ : GQp p →* GL (Fin 2) E) (i : ℤ) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (y : Fin 2 → ℂ_[p]) :
    y ∈ Ysp p ρ i K ↔ ∀ σ ∈ K.fixingSubgroup,
      matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 0 0 * y 0 + matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 0 * y 1 =
          cycPow p σ i • cpAct p σ (y 0) ∧
        matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 0 1 * y 0 + matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 1 * y 1 =
          cycPow p σ i • cpAct p σ (y 1) := by
  constructor
  · intro hy σ hσ
    have h := hy σ hσ
    exact ⟨by rw [← transpose_mulVec_zero, h]; rfl, by rw [← transpose_mulVec_one, h]; rfl⟩
  · intro hy σ hσ
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [transpose_mulVec_zero]; exact (hy σ hσ).1
    · rw [transpose_mulVec_one]; exact (hy σ hσ).2

theorem matC_apply (M : Matrix (Fin 2) (Fin 2) E) (a b : Fin 2) :
    matC p M a b = algebraMap E ℂ_[p] (M a b) := rfl

/-- The `E`-linear coordinate projection `y ↦ y_m e_m`. -/
def prj (m : Fin 2) : (Fin 2 → ℂ_[p]) →ₗ[E] (Fin 2 → ℂ_[p]) :=
  (LinearMap.single E (fun _ : Fin 2 => ℂ_[p]) m).comp (LinearMap.proj m)

theorem prj_apply (m : Fin 2) (y : Fin 2 → ℂ_[p]) : prj p (E := E) m y = Pi.single m (y m) := rfl

theorem prj_self (m : Fin 2) (y : Fin 2 → ℂ_[p]) : prj p (E := E) m y m = y m := by
  simp [prj_apply]

theorem prj_ne {m m' : Fin 2} (h : m' ≠ m) (y : Fin 2 → ℂ_[p]) : prj p (E := E) m y m' = 0 := by
  simp [prj_apply, Pi.single_apply, h]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`dim Y_i(ρ) ≤ dim Y_i(ρ^{ss})`** for `ρ` upper triangular with diagonal part `d`. -/
theorem finrank_Ysp_le_diag (hT : TateTwistInvariants) (hA : AxSenTate) [FiniteDimensional ℚ_[p] E]
    (ρ d : GQp p →* GL (Fin 2) E)
    (h10 : ∀ σ, (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0)
    (hd00 : ∀ σ, (d σ : Matrix (Fin 2) (Fin 2) E) 0 0 = (ρ σ : Matrix (Fin 2) (Fin 2) E) 0 0)
    (hd11 : ∀ σ, (d σ : Matrix (Fin 2) (Fin 2) E) 1 1 = (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 1)
    (hd01 : ∀ σ, (d σ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0)
    (hd10 : ∀ σ, (d σ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0) (i : ℤ) :
    finrank E (Ysp p ρ i E) ≤ finrank E (Ysp p d i E) := by
  classical
  haveI : FiniteDimensional E (Ysp p ρ i E) := Ysp_finiteDimensional p hT hA E ρ i
  haveI : FiniteDimensional E (Ysp p d i E) := Ysp_finiteDimensional p hT hA E d i
  set Yr := Ysp p ρ i E
  set Yd := Ysp p d i E
  have c0 : ∀ σ, matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := fun σ => by
    rw [matC_apply, h10, map_zero]
  have e00 : ∀ σ, matC p (d σ : Matrix (Fin 2) (Fin 2) E) 0 0 = matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 0 0 :=
    fun σ => by rw [matC_apply, matC_apply, hd00]
  have e11 : ∀ σ, matC p (d σ : Matrix (Fin 2) (Fin 2) E) 1 1 = matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 1 :=
    fun σ => by rw [matC_apply, matC_apply, hd11]
  have z01 : ∀ σ, matC p (d σ : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := fun σ => by
    rw [matC_apply, hd01, map_zero]
  have z10 : ∀ σ, matC p (d σ : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := fun σ => by
    rw [matC_apply, hd10, map_zero]
  -- membership in `Y_i(d)` splits into the two coordinates
  have memd : ∀ y : Fin 2 → ℂ_[p], y ∈ Yd ↔ ∀ σ ∈ E.fixingSubgroup,
      matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 0 0 * y 0 = cycPow p σ i • cpAct p σ (y 0) ∧
      matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 1 * y 1 = cycPow p σ i • cpAct p σ (y 1) := by
    intro y
    rw [mem_Ysp_two]
    refine forall₂_congr fun σ _ => ?_
    rw [e00, e11, z01, z10, zero_mul, zero_mul, add_zero, zero_add]
  have memr : ∀ y : Fin 2 → ℂ_[p], y ∈ Yr ↔ ∀ σ ∈ E.fixingSubgroup,
      matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 0 0 * y 0 = cycPow p σ i • cpAct p σ (y 0) ∧
      matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 0 1 * y 0 + matC p (ρ σ : Matrix (Fin 2) (Fin 2) E) 1 1 * y 1 =
        cycPow p σ i • cpAct p σ (y 1) := by
    intro y
    rw [mem_Ysp_two]
    refine forall₂_congr fun σ _ => ?_
    rw [c0, zero_mul, add_zero]
  -- (a) `y ∈ Y(ρ) ⇒ y₀ e₀ ∈ Y(d)`
  have ha : ∀ y ∈ Yr, prj p (E := E) 0 y ∈ Yd := by
    intro y hy
    rw [memd]
    intro σ hσ
    obtain ⟨h1, -⟩ := (memr y).1 hy σ hσ
    rw [prj_self, prj_ne p (by decide), map_zero, smul_zero, mul_zero]
    exact ⟨h1, rfl⟩
  -- (b) `y ∈ Y(ρ)`, `y₀ = 0` ⇒ `y ∈ Y(d)`
  have hb : ∀ y ∈ Yr, y 0 = 0 → y ∈ Yd := by
    intro y hy h0
    rw [memd]
    intro σ hσ
    obtain ⟨-, h2⟩ := (memr y).1 hy σ hσ
    rw [h0, mul_zero, zero_add] at h2
    rw [h0, mul_zero, map_zero, smul_zero]
    exact ⟨rfl, h2⟩
  -- (c) `Y(d)` is stable under both projections
  have hc : ∀ m : Fin 2, ∀ y ∈ Yd, prj p (E := E) m y ∈ Yd := by
    intro m y hy
    rw [memd] at hy ⊢
    intro σ hσ
    obtain ⟨h1, h2⟩ := hy σ hσ
    fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [prj_self, prj_ne p (by decide), map_zero, smul_zero, mul_zero]
      exact ⟨h1, rfl⟩
    · simp only [Fin.mk_one, Fin.isValue]
      rw [prj_self, prj_ne p (by decide), map_zero, smul_zero, mul_zero]
      exact ⟨rfl, h2⟩
  have hsplit : ∀ y : Fin 2 → ℂ_[p], prj p (E := E) 0 y + prj p (E := E) 1 y = y := by
    intro y; funext m; fin_cases m <;> simp [prj_apply]
  -- `A = Y(d) ∩ ker pr₁`, `B = Y(d) ∩ ker pr₀`, `A ⊕ B = Y(d)`
  set A : Submodule E (Fin 2 → ℂ_[p]) := Yd ⊓ LinearMap.ker (prj p (E := E) 1)
  set B : Submodule E (Fin 2 → ℂ_[p]) := Yd ⊓ LinearMap.ker (prj p (E := E) 0)
  haveI : FiniteDimensional E A :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  haveI : FiniteDimensional E B :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  have hAB : finrank E A + finrank E B = finrank E Yd := by
    have hsup : A ⊔ B = Yd := by
      apply le_antisymm (sup_le inf_le_left inf_le_left)
      intro y hy
      rw [← hsplit y]
      refine Submodule.add_mem_sup ⟨hc 0 y hy, ?_⟩ ⟨hc 1 y hy, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker]; funext m; fin_cases m <;> simp [prj_apply]
      · rw [SetLike.mem_coe, LinearMap.mem_ker]; funext m; fin_cases m <;> simp [prj_apply]
    have hinf : A ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨⟨-, h1⟩, ⟨-, h0⟩⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at h1 h0
      rw [Submodule.mem_bot, ← hsplit y, h0, h1, add_zero]
    have := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hsup, hinf, finrank_bot, add_zero] at this
    exact this.symm
  -- rank–nullity for `pr₀` on `Y(ρ)`
  set f := (prj p (E := E) 0).domRestrict Yr
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrange : finrank E (LinearMap.range f) ≤ finrank E A := by
    have hle : LinearMap.range f ≤ A := by
      rintro _ ⟨y, rfl⟩
      refine ⟨ha y.1 y.2, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext m; fin_cases m <;> simp [f, prj_apply]
    exact LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  have hker : finrank E (LinearMap.ker f) ≤ finrank E B := by
    let g : LinearMap.ker f →ₗ[E] B :=
      LinearMap.codRestrict B (Yr.subtype.comp (LinearMap.ker f).subtype) (fun x => by
        have hx := x.2
        rw [LinearMap.mem_ker] at hx
        have hx' : prj p (E := E) 0 (x.1.1) = 0 := hx
        have h0 : (x.1.1 : Fin 2 → ℂ_[p]) 0 = 0 := by
          have := congrFun hx' 0
          rwa [prj_self] at this
        refine ⟨hb x.1.1 x.1.2 h0, ?_⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        exact hx')
    refine LinearMap.finrank_le_finrank_of_injective (f := g) ?_
    intro x x' hxx'
    have := congrArg (fun z : B => (z : Fin 2 → ℂ_[p])) hxx'
    exact Subtype.ext (Subtype.ext this)
  omega

end LocalSS

end

end EigenformHTPrinted

/-! ## §6c. The semisimplification of a `2`-dimensional Hodge–Tate representation -/

namespace EigenformHTPrinted

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

section GlobalHT

variable {ℓ : ℕ} [Fact ℓ.Prime]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The diagonal part of an upper triangular Hodge–Tate representation is Hodge–Tate with the same
weights** (`finrank_Ysp_le_diag` with the Tate–Sen bound `sum_finrank_Ysp_le`). -/
theorem ht_diag (ρ d : GaloisRep ℓ 2) (h10 : ∀ σ, ρ.mat σ 1 0 = 0)
    (hd00 : ∀ σ, d.mat σ 0 0 = ρ.mat σ 0 0) (hd11 : ∀ σ, d.mat σ 1 1 = ρ.mat σ 1 1)
    (hd01 : ∀ σ, d.mat σ 0 1 = 0) (hd10 : ∀ σ, d.mat σ 1 0 = 0)
    (S : Multiset ℤ) (hS : S.card = 2) (hρ : ρ.HasHTWeightsAtSelf ℓ S) : d.HasHTWeightsAtSelf ℓ S := by
  classical
  obtain ⟨E₁, hE₁, ρ₁, h₁, hw₁⟩ := hρ
  let E := IntermediateField.normalClosure ℚ_[ℓ] E₁ (PadicAlgCl ℓ)
  haveI : FiniteDimensional ℚ_[ℓ] E := inferInstance
  haveI : IsGalois ℚ_[ℓ] E := IsGalois.mk
  have hE₁E : E₁ ≤ E := IntermediateField.le_normalClosure E₁
  let ρL := ρ.restrictLocal ℓ
  let dL := d.restrictLocal ℓ
  have hent₁ : ∀ σ i j, (((ρ₁ σ : Matrix (Fin 2) (Fin 2) E₁) i j : E₁) : PadicAlgCl ℓ) =
      (ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j := by
    intro σ i j; rw [← h₁ σ]; rfl
  have hmem : ∀ σ i j, (ρL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j ∈ E := by
    intro σ i j; rw [← hent₁]
    exact hE₁E ((ρ₁ σ : Matrix (Fin 2) (Fin 2) E₁) i j).2
  have hmem' : ∀ σ i j, (dL σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j ∈ E := by
    intro σ
    change ∀ i j, d.mat (decomp ℓ σ) i j ∈ E
    rw [Fin.forall_fin_two]
    refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · rw [hd00]; exact hmem σ 0 0
    · rw [hd01]; exact zero_mem E
    · rw [hd10]; exact zero_mem E
    · rw [hd11]; exact hmem σ 1 1
  let ρE := liftGL E ρL hmem
  let dE := liftGL E dL hmem'
  have hwE : ∀ w, htMult ℓ ρE w = S.count w := fun w =>
    (htMult_eq_of_lifts ℓ ρL ρE ρ₁ (liftGL_map E ρL hmem) h₁ w).trans (hw₁ w)
  have hdY : ∀ i, finrank E (Ysp ℓ ρE i E) = S.count (-i) := by
    intro i; rw [← hwE, htMult_eq_finrank_Ysp ℓ tate axSen E ρE (-i), neg_neg]
  have hle : ∀ i, finrank E (Ysp ℓ ρE i E) ≤ finrank E (Ysp ℓ dE i E) := by
    refine finrank_Ysp_le_diag ℓ tate axSen ρE dE (fun σ => ?_) (fun σ => ?_) (fun σ => ?_)
      (fun σ => ?_) (fun σ => ?_)
    · apply Subtype.ext; rw [liftGL_coe]; exact h10 _
    · apply Subtype.ext; rw [liftGL_coe, liftGL_coe]; exact hd00 _
    · apply Subtype.ext; rw [liftGL_coe, liftGL_coe]; exact hd11 _
    · apply Subtype.ext; rw [liftGL_coe]; exact hd01 _
    · apply Subtype.ext; rw [liftGL_coe]; exact hd10 _
  refine ⟨E, inferInstance, dE, liftGL_map E dL hmem', fun w => ?_⟩
  rw [htMult_eq_finrank_Ysp ℓ tate axSen E dE w]
  have hcnt : ∀ j : ℤ, S.count (-j) = (S.map fun x : ℤ => -x).count j := by
    intro j
    have := Multiset.count_map_eq_count' (fun x : ℤ => -x) S neg_injective (-j)
    simp only [neg_neg] at this
    exact this.symm
  let J : Finset ℤ := insert (-w) (S.map fun x : ℤ => -x).toFinset
  have hsumR : ∑ j ∈ J, finrank E (Ysp ℓ ρE j E) = 2 := by
    simp only [hdY, hcnt]
    rw [← Finset.sum_subset (Finset.subset_insert _ _) (fun j _ hj => Multiset.count_eq_zero.2
      (fun h => hj (Multiset.mem_toFinset.2 h))), Multiset.toFinset_sum_count_eq, Multiset.card_map, hS]
  have hsumD := sum_finrank_Ysp_le ℓ tate axSen E dE J
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).1
    (le_antisymm (Finset.sum_le_sum fun j _ => hle j) (hsumD.trans hsumR.ge))
  rw [← heq (-w) (Finset.mem_insert_self _ _), hdY, neg_neg]

/-- **Semisimplification (dimension `2`).** Every `2`-dimensional `ρ` with Hodge–Tate weights `S` has a
semisimple `ρ'` with the same traces, unramified wherever `ρ` is, and with Hodge–Tate weights `S`. -/
theorem exists_ss (ρ : GaloisRep ℓ 2) (S : Multiset ℤ) (hS : S.card = 2) (hρ : ρ.HasHTWeightsAtSelf ℓ S) :
    ∃ ρ' : GaloisRep ℓ 2, ρ'.IsSemisimple ∧ ρ'.HasHTWeightsAtSelf ℓ S ∧
      (∀ σ, (ρ'.mat σ).trace = (ρ.mat σ).trace) ∧ (∀ τ, ρ.toHom τ = 1 → ρ'.toHom τ = 1) := by
  by_cases hss : ρ.IsSemisimple
  · exact ⟨ρ, hss, hρ, fun _ => rfl, fun _ h => h⟩
  obtain ⟨w, hw0, hw⟩ := exists_invariant_line ρ hss
  obtain ⟨P, hP⟩ := exists_gl_col w hw0
  have hc10 : ∀ σ, (conjGR ρ P).mat σ 1 0 = 0 := by
    intro σ
    obtain ⟨c, hc⟩ := hw σ
    have key : ((conjGR ρ P).mat σ).mulVec (Pi.single 0 1) = c • Pi.single 0 1 := by
      rw [conjGR_mat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hc, Matrix.mulVec_smul, ← hP,
        Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have := congrFun key 1
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  have hHTc := htConj_proof ℓ 2 ρ (conjGR ρ P) S (isConj_conjGR ρ P) hρ
  refine ⟨diagGR (conjGR ρ P) hc10,
    isSemisimple_of_diag _ (fun σ => by simp [diagGR_mat]) (fun σ => by simp [diagGR_mat]),
    ht_diag (conjGR ρ P) (diagGR (conjGR ρ P) hc10) hc10 (fun σ => by simp [diagGR_mat])
      (fun σ => by simp [diagGR_mat]) (fun σ => by simp [diagGR_mat]) (fun σ => by simp [diagGR_mat])
      S hS hHTc, fun σ => ?_, fun τ hτ => ?_⟩
  · have e : ((conjGR ρ P).mat σ).trace = (ρ.mat σ).trace := by
      rw [conjGR_mat, Matrix.trace_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    rw [← e, diagGR_mat, Matrix.trace_fin_two, Matrix.trace_fin_two]
    simp
  · have hc1 : (conjGR ρ P).mat τ = 1 := by
      rw [conjGR_mat, GaloisRep.mat, hτ, Units.val_one, mul_one, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    apply Units.ext
    change (diagGR (conjGR ρ P) hc10).mat τ = 1
    rw [diagGR_mat, hc1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end GlobalHT

end

end EigenformHTPrinted

/-! ## §7. The new leaf (printed existence form, reading-robust) and the discharge -/

namespace EigenformHTPrinted

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

/-- **New leaf (R13, printed existence form, robust to every reading).** Galois representations attached to
newforms are Hodge–Tate at `ℓ` with weights `0, k − 1`, every level (`ℓ ∣ N` included): for a prime `ℓ`,
embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`, and a newform `f ∈ S_k(Γ₁(N))` of weight `k ≥ 2` (Tau Ceti's printed
`HeckeRing.GL2.Newform N k`: a normalized Hecke eigenform in the Petersson complement of the old space), **there
is** a continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)`, unramified at every `p ∤ Nℓ`, whose Frobenius traces are `a_p(f)`
(read through `ιC`, `ιL`), and whose restriction to `G_{ℚ_ℓ}` is Hodge–Tate with weights `0` and `k − 1`.

Lean form: Hodge–Tate weights are the kernel's `HasHTWeightsAtSelf` (Tate's `dim (ℂ_ℓ(w) ⊗ V)^{G_{ℚ_ℓ}}`, the
cyclotomic character has weight `−1`, so weight `w` occurs iff `gr^w D_dR(V) ≠ 0`); `IsArithFrob σ v p` is an
arithmetic Frobenius at a place `v` of `ℚ̄` over `p`. **Reading-robust clauses** (so that no printed wording is
weaker than the leaf):
* *normalization*: the conclusion is the disjunction of the two self-consistent normalizations — arithmetic
  Frobenius `σ` has trace `a_p` and the weights are `{0, 1 − k}` (Tate-module normalization, as Diamond–Shurman
  9.6.5), **or** geometric Frobenius `σ⁻¹` has trace `a_p` and the weights are `{0, k − 1}` (cohomological
  normalization, as Deligne's and Kato's `H¹_ét`). A print in either Frobenius normalization and either sign
  convention for weights is one of the two disjuncts once its convention is translated to `htMult`;
* *semisimplicity*: not asked (the semisimplification is handled in Lean, `exists_ss`);
* *Frobenius*: only the trace, in the form "if `ιC α = a_p` then `tr = ιL α`" (no algebraicity of `a_p` is
  asserted); the "characteristic polynomial `x² − a_p x + χ(p)p^{k−1}`" wording gives it (`trace_of_charpoly`);
* *embeddings*: a print stated for an isomorphism `ι : ℚ̄_ℓ ≅ ℂ` gives every pair `(ιC, ιL)` (extend
  `ιC ∘ ιL⁻¹` to `ℚ̄_ℓ ≅ ℂ`; STANDARD).

Sources (no network on this host: every number and wording UNVERIFIED unless said otherwise). Existence form as
printed: the theorem on representations attached to newforms in the surveys Taylor, *Galois representations*,
Ann. Fac. Sci. Toulouse Math. (6) 13 (2004), and Gee, *Modularity lifting theorems*, Essent. Number Theory 1
(2022) §2 (both UNVERIFIED). Content: Deligne 1971 (existence; Sém. Bourbaki 355), Faltings, Math. Ann. 278
(1987) (Hodge–Tate, `ℓ ∤ N`), Saito, Invent. Math. 129 (1997) (all levels), Kato, Astérisque 295 (2004) §§9.2-9.4,
(9.2.2), pp. 187-188 (de Rham at every level for `V_{F_λ}(f)`: read by the locator audit, row R13) and §11.3
(filtration jumps `0, k − 1`; UNVERIFIED). For prints about the étale-cohomological `V_{F_λ}(f)` (Kato, Saito),
the leaf is their consequence with witness `V_{F_λ}(f) ⊗_{F_λ} ℚ̄_ℓ` (∃-introduction). Replaces ht-exists's
`KatoHTExists` (which asked for a semisimple witness in one fixed normalization). -/
def ModularHTPrinted : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ ρ : GaloisRep ℓ 2,
      ((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧
          ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (ρ.mat σ).trace = ιL α) ∧
        ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧
          ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (ρ.mat σ⁻¹).trace = ιL α) ∧
        ρ.HasHTWeightsAtSelf ℓ {0, k - 1})

/-- The "characteristic polynomial" wording of the Frobenius clause gives the trace clause. -/
theorem trace_of_charpoly {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K) (a b : K)
    (h : M.charpoly = Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b) :
    M.trace = a := by
  rw [Matrix.trace_eq_neg_charpoly_coeff, h]
  simp [Polynomial.coeff_X, Polynomial.coeff_C]

section Steps

variable {ℓ : ℕ} [Fact ℓ.Prime] {ιC : Qbar →ₐ[ℚ] ℂ} {ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ} {N : ℕ} {k : ℤ}

/-- **Duality step** (GLUE, proved): a cohomologically normalized `ρ` (geometric Frobenius has trace `a_p`)
has arithmetically normalized contragredient. -/
theorem dual_arith_of_geom {f : CF N k} (ρ : GaloisRep ℓ 2)
    (hg : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∀ α : Qbar, ιC α = coeff f p →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) :
    ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → (dualGR ρ).UnramifiedAt p ∧ ∀ α : Qbar, ιC α = coeff f p →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          ((dualGR ρ).mat σ).trace = ιL α := by
  intro p hp hpN
  obtain ⟨hu, htr⟩ := hg p hp hpN
  refine ⟨fun v hv σ hσ => ?_, fun α hα v σ hv hσ => ?_⟩
  · have h1 := hu v hv σ⁻¹ ((v.inertiaSubgroup ℚ).inv_mem hσ)
    apply Units.ext
    change (ρ.mat ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹).transpose = 1
    have : ((σ⁻¹ : v.decompositionSubgroup ℚ) : GQ) = ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹ := rfl
    rw [GaloisRep.mat, ← this, h1, Units.val_one, Matrix.transpose_one]
  · rw [dualGR_mat, Matrix.trace_transpose, htr α hα v σ hv hσ]

/-- The universal trace clause and the algebraicity of the `a_p` give `AttachedTo`. -/
theorem attached_of_univ {f : CF N k} {ρ : GaloisRep ℓ 2}
    (halg : ∀ p : ℕ, ∃ α : Qbar, ιC α = coeff f p)
    (h : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∀ α : Qbar, ιC α = coeff f p →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ).trace = ιL α) :
    ρ.AttachedTo ιC ιL f := by
  intro p hp hpN
  obtain ⟨hu, htr⟩ := h p hp hpN
  obtain ⟨α, hα⟩ := halg p
  exact ⟨hu, α, hα, htr α hα⟩

/-- Same traces and unramified where `ρ₁` is: attached to the same form. -/
theorem attached_of_trace {f : CF N k} {ρ₁ ρ' : GaloisRep ℓ 2} (ha : ρ₁.AttachedTo ιC ιL f)
    (htr : ∀ σ, (ρ'.mat σ).trace = (ρ₁.mat σ).trace) (hun : ∀ τ, ρ₁.toHom τ = 1 → ρ'.toHom τ = 1) :
    ρ'.AttachedTo ιC ιL f := by
  intro p hp hpN
  obtain ⟨hu, α, hα, htr1⟩ := ha p hp hpN
  exact ⟨fun v hv σ hσ => hun _ (hu v hv σ hσ), α, hα, fun v σ hv hσ => (htr σ).trans (htr1 v σ hv hσ)⟩

/-- **Transport step** (GLUE, proved: Chebotarev + Brauer–Nesbitt `attachedConj_proof`, invariance of Hodge–Tate
weights under conjugation `htConj_proof`; ht-exists's `ht_of_attached`, verbatim). -/
theorem ht_of_attached (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (hN : 0 < N) (f : CF N k) (ρ₀ ρ : GaloisRep ℓ 2) (S : Multiset ℤ)
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

/-- The Fourier coefficients of a normalized eigenform of weight `≥ 2` are algebraic (from the LEAF field
`eigenformCoeffFieldFinite`: `K_f` is a number field). -/
theorem exists_alg_coeff (hK : DSCoeffExt.EigenformCoeffFieldFinite) (ιC : Qbar →ₐ[ℚ] ℂ)
    {χ : DirichletCharacter ℂ N} {f : CF N k} (hN : 0 < N) (hk : 2 ≤ k)
    (hf : IsNormalizedEigenform f χ) (n : ℕ) : ∃ α : Qbar, ιC α = coeff f n := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : FiniteDimensional ℚ (DSCoeffExt.coeffField f) :=
    hK N k χ f hk (DSCoeffExt.isNormalizedEigenformDS_of hf)
  exact DSCoeffExt.exists_pre ιC (DSCoeffExt.coeffField f) ⟨coeff f n, DSCoeffExt.coeff_mem_coeffField f n⟩

end Steps

/-- **The field `eigenformHTNew` from the printed existence form** (GLUE, all proved: newform dictionary
(newform-dict), algebraicity of `a_p` (LEAF field `eigenformCoeffFieldFinite`), dualization (`HTDual`, from Tate's
theorems, proved on main), semisimplification (§6), Chebotarev + Brauer–Nesbitt transport). -/
theorem eigenformHTNew_of_printed (h : ModularHTPrinted) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    EigenformHTNew := by
  intro ℓ _ ιC ιL N k χ f ρ hN hk hf hss hatt
  obtain ⟨_, g, rfl, -⟩ := (NewformDict.g9_isNewform_iff hN).mp hf
  have halg : ∀ p : ℕ, ∃ α : Qbar, ιC α = coeff (g.toCuspForm : CF N k) p :=
    exists_alg_coeff hK ιC hN hk hf.1
  obtain ⟨ρ₀, h₀⟩ := h ℓ ιC ιL N k g hk
  have key : ∃ ρ₁ : GaloisRep ℓ 2, ρ₁.AttachedTo ιC ιL (g.toCuspForm : CF N k) ∧
      ρ₁.HasHTWeightsAtSelf ℓ {0, 1 - k} := by
    rcases h₀ with ⟨ha, hHT⟩ | ⟨hg, hHT⟩
    · exact ⟨ρ₀, attached_of_univ halg ha, hHT⟩
    · refine ⟨dualGR ρ₀, attached_of_univ halg (dual_arith_of_geom ρ₀ hg), ?_⟩
      have h2 := htDual ℓ 2 ρ₀ {0, k - 1} (by simp) hHT
      have hS : (({0, k - 1} : Multiset ℤ).map Neg.neg) = {0, 1 - k} := by
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]
      rwa [hS] at h2
  obtain ⟨ρ₁, ha₁, hHT₁⟩ := key
  obtain ⟨ρ', hss', hHT', htr, hun⟩ := exists_ss ρ₁ {0, 1 - k} (by simp) hHT₁
  exact ht_of_attached ιC ιL hN _ ρ' ρ _ hss' (attached_of_trace ha₁ htr hun) hHT' hss hatt

/-- **Converse: the leaf is no stronger than the field**, over the LEAF fields `dsThm965Printed`,
`eigenformCoeffFieldFinite`, `dsThm966Printed` (existence of a semisimple attached `ρ`, through
`r14Det_of_printed`). -/
theorem printed_of_eigenformHTNew (hD : DSCoeffExt.DSThm965Printed)
    (hK : DSCoeffExt.EigenformCoeffFieldFinite) (hDS : DSCoeffExt.DSThm966Printed) (h : EigenformHTNew) :
    ModularHTPrinted := by
  intro ℓ _ ιC ιL N _ k g hk
  have hN : 0 < N := Nat.pos_of_neZero N
  have hnew : IsNewform (g.toCuspForm : CF N k) (MulChar.ofUnitHom g.χ) :=
    NewformDict.g9_isNewform_iff_pkgI4.mpr (NewformDict.isNewform_of_newform g)
  have hR : EigenformRepExists := eigenformRepExists_of_r14Det (r14Det_of_printed
    (DS965Weak.dsThm965_of_weak (DSCoeffExt.dsThm965Weak_of_printed hD hK))
    (DSCoeffExt.dsThm966_of_printed hDS))
  obtain ⟨ρ, hss, hatt⟩ := hR ℓ ιC ιL N k _ _ hN (by omega) hnew.1
  refine ⟨ρ, Or.inl ⟨fun p hp hpN => ?_, h ℓ ιC ιL N k _ _ ρ hN hk hnew hss hatt⟩⟩
  obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
  refine ⟨hu, fun β hβ v σ hv hσ => ?_⟩
  have hβα : β = α := by
    apply ιC.toRingHom.injective
    change ιC β = ιC α
    rw [hβ, hα]
  rw [hβα]
  exact htr v σ hv hσ

theorem printed_iff (hD : DSCoeffExt.DSThm965Printed) (hK : DSCoeffExt.EigenformCoeffFieldFinite)
    (hDS : DSCoeffExt.DSThm966Printed) : ModularHTPrinted ↔ EigenformHTNew :=
  ⟨fun h => eigenformHTNew_of_printed h hK, printed_of_eigenformHTNew hD hK hDS⟩

end

end EigenformHTPrinted

#print axioms EigenformHTPrinted.eigenformHTNew_of_printed
#print axioms EigenformHTPrinted.printed_of_eigenformHTNew
#print axioms EigenformHTPrinted.exists_ss
#print axioms EigenformHTPrinted.trace_of_charpoly
