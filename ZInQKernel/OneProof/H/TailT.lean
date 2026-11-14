import ZInQKernel.OneProof.H.TailS

/-! # OneProof H, leaf-fold7 part T: hodge-split, second half (`scratch/hodge-split/HodgeSplit.lean` from line 2064
(§16) to the end, verbatim apart from this banner, the reopened namespace/`open`s/`variable (p)` of the file header
(lines 20-29 and 112) and the dropped `#print axioms` lines).

`ZInQ.Contrib.HodgeSplit.hodge_rows_of_leaves` and the row theorems `finiteImageHT_of_tate`,
`t23_all_of_bdrInvariants`, `deRhamComparisonHT_of_leavesT`, `r14Det_of_printed`, `senTwist_of_tate`
(docs/research/hodge-split.md). Imports only kernel modules (through `TailS`). -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace ZInQ.Contrib.HodgeSplit

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## §16. H-51 proved: `SenTwist` from Tate's two theorems

Over `G_E` (`E ⊆ ℚ̄_p` finite Galois, containing the entries of `ρ`, `ρ'` and the values of `ψ`),
`E`-linear Hodge–Tate data in coordinates: `Y_i(ρ) = {y ∈ ℂ_pⁿ | ρ(σ)ᵀ y = χ(σ)^i σ(y), σ ∈ G_E}`.
Steps: (T) Tate–Sen independence: `E`-bases of the `Y_j` together are `ℂ_p`-independent (Tate's two
theorems); (B) `dim_ℚp Y_i(ρ) = dim_ℚp H_i(ρ)` (Dedekind's lemma and Galois descent), so the `Y_j(ρ')`
span `ℂ_pⁿ`; (X) a nonzero `y ∈ Y_{i₀}(ρ)`, expanded in that basis, gives `β ∈ ℂ_p^×` with
`σ(β) = ψ(σ)⁻¹ χ(σ)^s β`; (M) multiplication by `β⁻¹` maps `Y_i(ρ)` onto `Y_{i+s}(ρ')`. -/

section SenSec

variable {n : ℕ}

theorem cycPow_add (σ : GQp p) (a b : ℤ) : cycPow p σ (a + b) = cycPow p σ a * cycPow p σ b := by
  simp only [cycPow, zpow_add, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_neg_mul (σ : GQp p) (a : ℤ) : cycPow p σ (-a) * cycPow p σ a = 1 := by
  rw [← cycPow_add, neg_add_cancel, cycPow_zero]

/-- `σ` on `ℂ_pⁿ`, coordinatewise. -/
def vAct (σ : GQp p) (y : Fin n → ℂ_[p]) : Fin n → ℂ_[p] := fun k => cpAct p σ (y k)

theorem vAct_add (σ : GQp p) (y z : Fin n → ℂ_[p]) : vAct p σ (y + z) = vAct p σ y + vAct p σ z := by
  ext k; simp [vAct]

theorem vAct_smul (σ : GQp p) (c : ℂ_[p]) (y : Fin n → ℂ_[p]) :
    vAct p σ (c • y) = cpAct p σ c • vAct p σ y := by
  ext k; simp [vAct]

theorem vAct_sum {ι : Type*} (s : Finset ι) (σ : GQp p) (f : ι → Fin n → ℂ_[p]) :
    vAct p σ (∑ k ∈ s, f k) = ∑ k ∈ s, vAct p σ (f k) := by
  ext m; simp [vAct, Finset.sum_apply, map_sum]

theorem vAct_zero (σ : GQp p) : vAct p σ (0 : Fin n → ℂ_[p]) = 0 := by ext; simp [vAct]

/-- A matrix over `E` read in `ℂ_p`. -/
def matC {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (M : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) ℂ_[p] :=
  M.map (algebraMap E ℂ_[p])

/-- `Y_i(ρ)` over `G_K`: `{y ∈ ℂ_pⁿ | ρ(σ)ᵀ y = χ(σ)^i σ(y), σ ∈ G_K}`, a `K`-subspace. -/
def Ysp {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E) (i : ℤ)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Submodule K (Fin n → ℂ_[p]) where
  carrier := {y | ∀ σ ∈ K.fixingSubgroup,
    (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y = cycPow p σ i • vAct p σ y}
  zero_mem' σ _ := by simp [vAct_zero]
  add_mem' {y z} hy hz σ hσ := by
    rw [Matrix.mulVec_add, hy σ hσ, hz σ hσ, vAct_add, smul_add]
  smul_mem' a y hy σ hσ := by
    have ha : cpAct p σ (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a := by
      rw [IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq, cpAct_coe]
      congr 1
      exact hσ a
    rw [← algebraMap_smul (A := ℂ_[p]) a y, Matrix.mulVec_smul, hy σ hσ, vAct_smul, ha, smul_comm]

theorem matC_mul_inv {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E)
    (σ : GQp p) : matC p (ρ σ : Matrix (Fin n) (Fin n) E) * matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E) = 1 := by
  rw [matC, matC, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem matC_inv_mul {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E)
    (σ : GQp p) : matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E) * matC p (ρ σ : Matrix (Fin n) (Fin n) E) = 1 := by
  rw [matC, matC, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
    Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem transpose_mulVec_eq_zero {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) {x : Fin n → ℂ_[p]}
    (h : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec x = 0) : x = 0 := by
  have : (matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)).transpose.mulVec
      ((matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, matC_mul_inv, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [← this, h, Matrix.mulVec_zero]

theorem vAct_of_mem {E K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ρ : GQp p →* GL (Fin n) E}
    {i : ℤ} {y : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i K) {σ : GQp p} (hσ : σ ∈ K.fixingSubgroup) :
    vAct p σ y = cycPow p σ (-i) • (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y := by
  rw [hy σ hσ, smul_smul, cycPow_neg_mul, one_smul]

/-- **(T) Tate–Sen independence.** -/
theorem Ysp_linearIndependent (hT : TateTwistInvariants) (hA : AxSenTate)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι → ℤ) (y : ι → (Fin n → ℂ_[p]))
    (hy : ∀ k, y k ∈ Ysp p ρ (j k) K)
    (hind : ∀ (j₀ : ℤ) (a : ι → K), (∀ k, j k ≠ j₀ → a k = 0) → ∑ k, a k • y k = 0 →
      ∀ k, a k = 0) :
    LinearIndependent ℂ_[p] y := by
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ (s : Finset ι) (b : ι → ℂ_[p]), (∀ k ∉ s, b k = 0) → ∑ k, b k • y k = 0 →
      ∀ k, b k = 0 from fun b hb => H Finset.univ b (by simp) hb
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hbs hb
  by_contra hne
  push_neg at hne
  obtain ⟨k₀, hk₀⟩ := hne
  have hk₀s : k₀ ∈ s := by
    by_contra h; exact hk₀ (hbs k₀ h)
  let b' : ι → ℂ_[p] := fun k => (b k₀)⁻¹ * b k
  have hb' : ∑ k, b' k • y k = 0 := by
    simp only [b', mul_smul, ← Finset.smul_sum, hb, smul_zero]
  have hb'k₀ : b' k₀ = 1 := inv_mul_cancel₀ hk₀
  have hb's : ∀ k ∉ s, b' k = 0 := fun k hk => by simp [b', hbs k hk]
  have key : ∀ σ ∈ K.fixingSubgroup, ∀ k,
      b' k = cycPow p σ (j k₀ - j k) • cpAct p σ (b' k) := by
    intro σ hσ
    let d : ι → ℂ_[p] := fun k => b' k - cycPow p σ (j k₀ - j k) • cpAct p σ (b' k)
    have h1 : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec
        (∑ k, (cycPow p σ (-j k) • cpAct p σ (b' k)) • y k) = 0 := by
      have h0 := congrArg (vAct p σ) hb'
      rw [vAct_sum, vAct_zero] at h0
      rw [Matrix.mulVec_sum]
      rw [← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [vAct_smul, vAct_of_mem p (hy k) hσ, Matrix.mulVec_smul, smul_assoc, smul_comm]
    have h2 := transpose_mulVec_eq_zero p ρ σ h1
    have hd : ∑ k, d k • y k = 0 := by
      have h3 : ∑ k, (cycPow p σ (j k₀ - j k) • cpAct p σ (b' k)) • y k = 0 := by
        have e : ∀ k, (cycPow p σ (j k₀ - j k) • cpAct p σ (b' k)) • y k =
            cycPow p σ (j k₀) • ((cycPow p σ (-j k) • cpAct p σ (b' k)) • y k) := by
          intro k
          rw [← smul_assoc, smul_smul, ← cycPow_add, sub_eq_add_neg]
        simp only [e]
        rw [← Finset.smul_sum, h2, smul_zero]
      simp only [d, sub_smul, Finset.sum_sub_distrib, hb', h3, sub_zero]
    have hds : ∀ k ∉ s.erase k₀, d k = 0 := by
      intro k hk
      by_cases hkk : k = k₀
      · subst hkk
        simp [d, hb'k₀, cycPow_zero]
      · have : k ∉ s := fun h => hk (Finset.mem_erase.mpr ⟨hkk, h⟩)
        simp [d, hb's k this]
    have := ih (s.erase k₀) (Finset.erase_ssubset hk₀s) d hds hd
    intro k
    exact sub_eq_zero.mp (this k)
  have hzero : ∀ k, j k ≠ j k₀ → b' k = 0 := by
    intro k hk
    refine hT p K (j k₀ - j k) (by omega) (b' k) fun σ hσ => (key σ hσ k).symm
  have hKval : ∀ k, j k = j k₀ → ∃ a : K, b' k = algebraMap K ℂ_[p] a := by
    intro k hk
    obtain ⟨a, ha⟩ := hA p K (b' k) fun σ hσ => by
      have := key σ hσ k
      rw [hk, sub_self, cycPow_zero, one_smul] at this
      exact this.symm
    refine ⟨a, ?_⟩
    rw [ha, IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
    rfl
  classical
  let a : ι → K := fun k => if h : j k = j k₀ then (hKval k h).choose else 0
  have ha : ∀ k, j k = j k₀ → b' k = algebraMap K ℂ_[p] (a k) := by
    intro k hk
    simp only [a, dif_pos hk]
    exact (hKval k hk).choose_spec
  have hsum : ∑ k, a k • y k = 0 := by
    rw [← hb']
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : j k = j k₀
    · rw [ha k h, algebraMap_smul]
    · simp only [a, dif_neg h, zero_smul]
      rw [hzero k h, zero_smul]
  have h0 := hind (j k₀) a (fun k hk => by simp [a, dif_neg hk]) hsum k₀
  have h1 := ha k₀ rfl
  rw [h0, map_zero, hb'k₀] at h1
  exact one_ne_zero h1

end SenSec

section SenBridge

variable {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]

theorem eC_eq (e : E) : algebraMap E ℂ_[p] e = (((e : PadicAlgCl p)) : ℂ_[p]) := by
  rw [IsScalarTower.algebraMap_apply E (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
  rfl

theorem eC_smul (c : ℚ_[p]) (e : E) : algebraMap E ℂ_[p] (c • e) = c • algebraMap E ℂ_[p] e := by
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]

variable [IsGalois ℚ_[p] E]

theorem cpAct_eC (g : GQp p) (e : E) : cpAct p g (algebraMap E ℂ_[p] e) =
    algebraMap E ℂ_[p] (AlgEquiv.restrictNormalHom E g e) := by
  rw [eC_eq, eC_eq, cpAct_coe]
  congr 1
  exact (AlgEquiv.restrictNormal_commutes g E e).symm

/-- `ρ^τ`: `τ` applied to the entries. -/
def rhoTau (τ : E ≃ₐ[ℚ_[p]] E) (ρ : GQp p →* GL (Fin n) E) : GQp p →* GL (Fin n) E :=
  (Matrix.GeneralLinearGroup.map (τ : E →+* E)).comp ρ

theorem matC_rhoTau (τ : E ≃ₐ[ℚ_[p]] E) (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (a b : Fin n) :
    matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E) a b =
      algebraMap E ℂ_[p] (τ ((ρ σ : Matrix (Fin n) (Fin n) E) a b)) := rfl

/-- **Dedekind coordinates**: `y ↦ (v ↦ Σ_τ Σ_k y_τ,k · τ(v_k))`. -/
def LamC : ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) →ₗ[ℂ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun y :=
    { toFun := fun v => ∑ τ, ∑ k, y τ k * algebraMap E ℂ_[p] (τ (v k))
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        have hxs : ∀ (x : E ≃ₐ[ℚ_[p]] E) (e : E), x (c • e) = c • x e := fun x e => by
          rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]
        simp only [Pi.smul_apply, hxs, eC_smul, mul_smul_comm, Finset.smul_sum,
          RingHom.id_apply] }
  map_add' y z := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      LinearMap.add_apply]
  map_smul' c y := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, mul_assoc,
      Finset.mul_sum, LinearMap.smul_apply, RingHom.id_apply]

theorem LamC_apply (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) (v : Fin n → E) :
    LamC p E y v = ∑ τ, ∑ k, y τ k * algebraMap E ℂ_[p] (τ (v k)) := rfl

theorem LamC_injective : Function.Injective (LamC p E (n := n)) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot]
  -- Dedekind's independence of the characters `e ↦ τ(e)`
  let χτ : (E ≃ₐ[ℚ_[p]] E) → (E →* ℂ_[p]) := fun τ =>
    (algebraMap E ℂ_[p]).toMonoidHom.comp (τ : E →+* E).toMonoidHom
  have hχinj : Function.Injective χτ := by
    intro τ₁ τ₂ h
    exact AlgEquiv.ext fun e => (algebraMap E ℂ_[p]).injective
      (congrArg (fun f : E →* ℂ_[p] => f e) h)
  have hind := (linearIndependent_monoidHom E ℂ_[p]).comp χτ hχinj
  funext τ k
  have hk : ∀ e : E, ∑ τ, y τ k * algebraMap E ℂ_[p] (τ e) = 0 := by
    intro e
    have := LinearMap.congr_fun hy (Pi.single k e)
    rw [LamC_apply, LinearMap.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hm; simp [Pi.single_apply, hm]
    · intro h; exact absurd (Finset.mem_univ k) h
  have := Fintype.linearIndependent_iff.mp hind (fun τ => y τ k) (by
    funext e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    exact hk e)
  exact this τ

theorem LamC_surjective : Function.Surjective (LamC p E (n := n)) := by
  have h1 : Module.finrank ℂ_[p] ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) =
      Module.finrank ℂ_[p] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) := by
    rw [Module.finrank_linearMap, Module.finrank_pi_fintype, Module.finrank_self, mul_one,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Module.finrank_self, mul_one]
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h1).mp (LamC_injective p E)

end SenBridge

section SenBridge2

variable {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
  [IsGalois ℚ_[p] E]

theorem mem_fixing_iff_ker (σ : GQp p) :
    σ ∈ E.fixingSubgroup ↔ σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ_[p]) (K₁ := PadicAlgCl p) E).ker := by
  rw [IntermediateField.restrictNormalHom_ker]

theorem cpAct_eC_fix {σ : GQp p} (hσ : σ ∈ E.fixingSubgroup) (e : E) :
    cpAct p σ (algebraMap E ℂ_[p] e) = algebraMap E ℂ_[p] e := by
  rw [eC_eq, cpAct_coe]
  congr 1
  exact hσ e

/-- (I1) -/
theorem LamC_matRep (ρ : GQp p →* GL (Fin n) E) (σ : GQp p)
    (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) (v : Fin n → E) :
    LamC p E y (matRep p ρ σ v) =
      LamC p E (fun τ => (matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (y τ)) v := by
  rw [LamC_apply, LamC_apply, matRep_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matC_rhoTau, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- (I2) -/
theorem LamC_htAct (i : ℤ) {σ : GQp p} (hσ : σ ∈ E.fixingSubgroup)
    (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) (v : Fin n → E) :
    htAct p i σ (LamC p E y v) = LamC p E (fun τ => cycPow p σ i • vAct p σ (y τ)) v := by
  rw [htAct_apply, LamC_apply, LamC_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cpAct_eC_fix p E hσ, Pi.smul_apply, smul_mul_assoc]
  rfl

/-- **Membership in Dedekind coordinates.** -/
theorem LamC_mem_iff (ρ : GQp p →* GL (Fin n) E) (i : ℤ)
    (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) :
    LamC p E y ∈ Dsp (htAct p i) (matRep p ρ)
        ((AlgEquiv.restrictNormalHom (F := ℚ_[p]) (K₁ := PadicAlgCl p) E).ker : Set (GQp p)) ↔
      ∀ τ, y τ ∈ Ysp p (rhoTau p E τ ρ) i E := by
  constructor
  · intro h τ σ hσ
    have hσ' := (mem_fixing_iff_ker p E σ).mp hσ
    have h1 : LamC p E (fun τ => (matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (y τ)) =
        LamC p E (fun τ => cycPow p σ i • vAct p σ (y τ)) := by
      refine LinearMap.ext fun v => ?_
      rw [← LamC_matRep, ← LamC_htAct p E i hσ]
      exact h σ hσ' v
    exact congrFun (LamC_injective p E h1) τ
  · intro h σ hσ v
    have hσ' := (mem_fixing_iff_ker p E σ).mpr hσ
    rw [LamC_matRep, LamC_htAct p E i hσ']
    congr 2
    funext τ
    exact h τ σ hσ'

end SenBridge2

section SenBridge3

variable {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
  [IsGalois ℚ_[p] E]

theorem vAct_vAct (g h : GQp p) (y : Fin n → ℂ_[p]) : vAct p g (vAct p h y) = vAct p (g * h) y := by
  ext k; simp [vAct, cpAct_mul]

theorem vAct_one' (y : Fin n → ℂ_[p]) : vAct p 1 y = y := by
  ext k; simp [vAct, cpAct_one]

theorem vAct_qsmul (g : GQp p) (c : ℚ_[p]) (y : Fin n → ℂ_[p]) : vAct p g (c • y) = c • vAct p g y := by
  ext k; simp [vAct, cpAct_smul]

theorem vAct_mulVec (g : GQp p) (M : Matrix (Fin n) (Fin n) ℂ_[p]) (y : Fin n → ℂ_[p]) :
    vAct p g (M.mulVec y) = (M.map (cpAct p g)).mulVec (vAct p g y) := by
  ext k; simp [vAct, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem matC_transpose_map (g : GQp p) (M : Matrix (Fin n) (Fin n) E) :
    (matC p M).transpose.map (cpAct p g) =
      (matC p (M.map (AlgEquiv.restrictNormalHom E g : E →+* E))).transpose := by
  ext a b; simp [matC, cpAct_eC]

theorem matC_transpose_map_fix {σ : GQp p} (hσ : σ ∈ E.fixingSubgroup) (M : Matrix (Fin n) (Fin n) E) :
    (matC p M).transpose.map (cpAct p σ) = (matC p M).transpose := by
  ext a b; simp [matC, cpAct_eC_fix p E hσ]

theorem cycPow_conj (g σ : GQp p) (i : ℤ) : cycPow p (g * σ * g⁻¹) i = cycPow p σ i := by
  rw [ZInQ.Contrib.G9.PkgI4.cycPow_mul, ZInQ.Contrib.G9.PkgI4.cycPow_mul, mul_comm (cycPow p g i), mul_assoc,
    ← ZInQ.Contrib.G9.PkgI4.cycPow_mul, mul_inv_cancel, ZInQ.Contrib.G9.PkgI4.cycPow_one, mul_one]

theorem conj_mem_fixing {g σ : GQp p} (hσ : σ ∈ E.fixingSubgroup) : g * σ * g⁻¹ ∈ E.fixingSubgroup := by
  rw [mem_fixing_iff_ker] at hσ ⊢
  exact (AlgEquiv.restrictNormalHom E).normal_ker.conj_mem σ hσ g

theorem matC_mul (A B : Matrix (Fin n) (Fin n) E) : matC p (A * B) = matC p A * matC p B := by
  simp [matC, Matrix.map_mul]

/-- **Conjugation.** `dim_ℚp Y_i(ρ^τ) = dim_ℚp Y_i(ρ)`. -/
theorem finrank_Ysp_rhoTau (ρ : GQp p →* GL (Fin n) E) (i : ℤ) (τ : E ≃ₐ[ℚ_[p]] E) :
    Module.finrank ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) = Module.finrank ℚ_[p] (Ysp p ρ i E) := by
  have hγ : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ_[p]) (K₁ := PadicAlgCl p) E) :=
    AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)
  obtain ⟨g, hg⟩ := hγ τ
  let A := (matC p (ρ g : Matrix (Fin n) (Fin n) E)).transpose
  let A' := (matC p (ρ g⁻¹ : Matrix (Fin n) (Fin n) E)).transpose
  have hAA' : A * A' = 1 := by
    simp only [A, A', ← Matrix.transpose_mul, matC_inv_mul, Matrix.transpose_one]
  have hA'A : A' * A = 1 := by
    simp only [A, A', ← Matrix.transpose_mul, matC_mul_inv, Matrix.transpose_one]
  have hmatτ : ∀ σ, (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.map (cpAct p g) =
      (matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose := by
    intro σ
    rw [matC_transpose_map, hg]
    rfl
  have hρmul : ∀ a b, matC p (ρ (a * b) : Matrix (Fin n) (Fin n) E) =
      matC p (ρ a : Matrix (Fin n) (Fin n) E) * matC p (ρ b : Matrix (Fin n) (Fin n) E) := by
    intro a b; rw [map_mul, Units.val_mul, matC_mul]
  -- forward map
  have hF : ∀ y ∈ Ysp p (rhoTau p E τ ρ) i E, A.mulVec (vAct p g⁻¹ y) ∈ Ysp p ρ i E := by
    intro y hy σ' hσ'
    set σ := g * σ' * g⁻¹
    have hσ : σ ∈ E.fixingSubgroup := conj_mem_fixing p E hσ'
    have e1 : (matC p (ρ σ' : Matrix (Fin n) (Fin n) E)).transpose * A =
        A * (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose := by
      simp only [A, ← Matrix.transpose_mul, ← hρmul]
      congr 2; simp [σ, mul_assoc]
    have e2 : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (vAct p g⁻¹ y) =
        vAct p g⁻¹ ((matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y) := by
      rw [← hmatτ, vAct_mulVec, Matrix.map_map]
      congr 1
      exact Matrix.ext fun a b => (cpAct_inv_apply p g _).symm
    rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, e2, hy σ hσ, vAct_qsmul, vAct_vAct,
      Matrix.mulVec_smul, cycPow_conj]
    have e3 : g⁻¹ * σ = σ' * g⁻¹ := by simp [σ, mul_assoc]
    rw [e3, ← vAct_vAct]
    congr 1
    rw [vAct_mulVec, matC_transpose_map_fix p E hσ']
  -- backward map
  have hF' : ∀ w ∈ Ysp p ρ i E, vAct p g (A'.mulVec w) ∈ Ysp p (rhoTau p E τ ρ) i E := by
    intro w hw σ hσ
    set σ'' := g⁻¹ * σ * g
    have hσ'' : σ'' ∈ E.fixingSubgroup := by
      have := conj_mem_fixing p E (g := g⁻¹) hσ
      simpa [σ''] using this
    have e1 : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose * A' =
        A' * (matC p (ρ σ'' : Matrix (Fin n) (Fin n) E)).transpose := by
      simp only [A', ← Matrix.transpose_mul, ← hρmul]
      congr 2; simp [σ'', mul_assoc]
    rw [← hmatτ, ← vAct_mulVec, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, hw σ'' hσ'',
      Matrix.mulVec_smul, vAct_qsmul]
    have e3 : (A'.mulVec (vAct p σ'' w)) = vAct p σ'' (A'.mulVec w) := by
      rw [vAct_mulVec, matC_transpose_map_fix p E hσ'']
    rw [e3, vAct_vAct, vAct_vAct]
    have e4 : g * σ'' = σ * g := by simp [σ'', mul_assoc]
    have e5 : cycPow p σ'' i = cycPow p σ i := by
      have := cycPow_conj p g⁻¹ σ i
      simpa [σ''] using this
    rw [e4, e5]
  let e : Ysp p (rhoTau p E τ ρ) i E ≃ₗ[ℚ_[p]] Ysp p ρ i E :=
    { toFun := fun y => ⟨A.mulVec (vAct p g⁻¹ y), hF y y.2⟩
      invFun := fun w => ⟨vAct p g (A'.mulVec w), hF' w w.2⟩
      map_add' := fun y z => by
        apply Subtype.ext
        simp only [Submodule.coe_add, vAct_add, Matrix.mulVec_add]
      map_smul' := fun c y => by
        apply Subtype.ext
        show A.mulVec (vAct p g⁻¹ (c • (y : Fin n → ℂ_[p]))) = c • A.mulVec (vAct p g⁻¹ y)
        rw [vAct_qsmul, Matrix.mulVec_smul]
      left_inv := fun y => by
        apply Subtype.ext
        simp only [Matrix.mulVec_mulVec, hA'A, Matrix.one_mulVec, vAct_vAct, mul_inv_cancel,
          vAct_one']
      right_inv := fun w => by
        apply Subtype.ext
        simp only [vAct_vAct, inv_mul_cancel, vAct_one', Matrix.mulVec_mulVec, hAA',
          Matrix.one_mulVec] }
  exact e.finrank_eq

end SenBridge3

section SenBridge4

variable {n : ℕ}

/-- `Y_i(ρ)` is finite-dimensional over `K` (from (T): `dim_K ≤ n`). -/
theorem Ysp_finiteDimensional (hT : TateTwistInvariants) (hA : AxSenTate)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    FiniteDimensional K (Ysp p ρ i K) := by
  classical
  haveI : Module.Free K (Ysp p ρ i K) := Module.Free.of_divisionRing K _
  refine Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt (rank_le (n := n) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0 (n := n)))
  -- the vectors of `s` are `ℂ_p`-independent
  have hli : LinearIndependent ℂ_[p] (fun x : s => ((x : Ysp p ρ i K) : Fin n → ℂ_[p])) := by
    refine Ysp_linearIndependent p hT hA K ρ (fun _ => i) _ (fun x => (x : Ysp p ρ i K).2) ?_
    intro j₀ a _ hsum
    have h1 : ∑ k : s, a k • (k : Ysp p ρ i K) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul]
      exact hsum
    exact Fintype.linearIndependent_iff.mp hs a h1
  calc s.card = Fintype.card s := (Fintype.card_coe s).symm
    _ ≤ Module.finrank ℂ_[p] (Fin n → ℂ_[p]) := hli.fintype_card_le_finrank
    _ = n := Module.finrank_fin_fun _

variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

/-- **(B) the bridge.** `dim_ℚp H_i(ρ) = dim_ℚp Y_i(ρ)`, for `E` finite Galois. -/
theorem finrank_htSpace_eq_Ysp (hT : TateTwistInvariants) (hA : AxSenTate)
    (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    Module.finrank ℚ_[p] (htSpace p ρ i) = Module.finrank ℚ_[p] (Ysp p ρ i E) := by
  classical
  haveI : ∀ τ : E ≃ₐ[ℚ_[p]] E, FiniteDimensional E (Ysp p (rhoTau p E τ ρ) i E) :=
    fun τ => Ysp_finiteDimensional p hT hA E _ i
  haveI : ∀ τ : E ≃ₐ[ℚ_[p]] E, FiniteDimensional ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) :=
    fun τ => Module.Finite.trans E _
  let γ : GQp p →* (E ≃ₐ[ℚ_[p]] E) := AlgEquiv.restrictNormalHom E
  have hγ : Function.Surjective γ := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)
  have hsemi : ∀ g x b, htAct p i g (iotaK p E x * b) = iotaK p E (γ g x) * htAct p i g b := by
    intro g x b
    rw [iotaK, AlgHom.comp_apply, htAct_semi, AlgHom.comp_apply]
    congr 2
    exact (AlgEquiv.restrictNormal_commutes g E x).symm
  have hdesc := descent_finrank (htAct p i) (matRep p ρ) (iotaK p E) γ hγ hsemi
  rw [← htSpace_eq_DspMat] at hdesc
  -- `Dsp(G_E)` in Dedekind coordinates
  let P : Submodule ℚ_[p] ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) :=
    { carrier := {y | ∀ τ, y τ ∈ Ysp p (rhoTau p E τ ρ) i E}
      zero_mem' := fun τ => (Ysp p (rhoTau p E τ ρ) i E).zero_mem
      add_mem' := fun ha hb τ => (Ysp p (rhoTau p E τ ρ) i E).add_mem (ha τ) (hb τ)
      smul_mem' := fun c y hy τ => by
        have := (Ysp p (rhoTau p E τ ρ) i E).smul_mem (algebraMap ℚ_[p] E c) (hy τ)
        rw [algebraMap_smul] at this
        exact this }
  let L := (LamC p E (n := n)).restrictScalars ℚ_[p]
  have hmap : Submodule.map L P = Dsp (htAct p i) (matRep p ρ) (γ.ker : Set (GQp p)) := by
    ext φ
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (LamC_mem_iff p E ρ i y).mpr hy
    · intro hφ
      obtain ⟨y, rfl⟩ := LamC_surjective p E φ
      exact ⟨y, (LamC_mem_iff p E ρ i y).mp hφ, rfl⟩
  have hfinP : Module.finrank ℚ_[p] P =
      ∑ τ : E ≃ₐ[ℚ_[p]] E, Module.finrank ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) := by
    let ι : (∀ τ : E ≃ₐ[ℚ_[p]] E, Ysp p (rhoTau p E τ ρ) i E) →ₗ[ℚ_[p]]
        ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) :=
      { toFun := fun x τ => (x τ : Fin n → ℂ_[p])
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hinj : Function.Injective ι := fun x y h => funext fun τ => Subtype.ext (congrFun h τ)
    have hrange : LinearMap.range ι = P := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩ τ; exact (x τ).2
      · intro hy; exact ⟨fun τ => ⟨y τ, hy τ⟩, rfl⟩
    haveI : ∀ τ : E ≃ₐ[ℚ_[p]] E, Module.Free ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) :=
      fun τ => Module.Free.of_divisionRing _ _
    rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
  have hDsp : Module.finrank ℚ_[p] (Dsp (htAct p i) (matRep p ρ) (γ.ker : Set (GQp p))) =
      Module.finrank ℚ_[p] E * Module.finrank ℚ_[p] (Ysp p ρ i E) := by
    rw [← hmap, ← (Submodule.equivMapOfInjective L (LamC_injective p E) P).finrank_eq, hfinP]
    simp only [finrank_Ysp_rhoTau p E ρ i, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  have hE : 0 < Module.finrank ℚ_[p] E := Module.finrank_pos
  rw [hDsp] at hdesc
  exact (Nat.eq_of_mul_eq_mul_left hE hdesc).symm

end SenBridge4

section SenFinal

variable {n : ℕ}

/-- **Θ is onto.** If `Σ_{j ∈ J} dim_K Y_j = n`, the `K`-bases of the `Y_j` form a `ℂ_p`-basis. -/
theorem exists_basis_Ysp (hT : TateTwistInvariants) (hA : AxSenTate)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E) (J : Finset ℤ)
    (hsum : ∑ j ∈ J, Module.finrank K (Ysp p ρ j K) = n) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p])) (j : ι → ℤ),
      ∀ k, b k ∈ Ysp p ρ (j k) K := by
  classical
  haveI : ∀ j : ℤ, FiniteDimensional K (Ysp p ρ j K) := fun j => Ysp_finiteDimensional p hT hA K ρ j
  haveI : ∀ j : ℤ, Module.Free K (Ysp p ρ j K) := fun j => Module.Free.of_divisionRing _ _
  let d : J → ℕ := fun jj => Module.finrank K (Ysp p ρ jj K)
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
  have hcard : Fintype.card (Σ jj : J, Fin (d jj)) = Module.finrank ℂ_[p] (Fin n → ℂ_[p]) := by
    rw [Fintype.card_sigma, Module.finrank_fin_fun]
    simp only [Fintype.card_fin, d]
    rw [Finset.sum_coe_sort J (fun j => Module.finrank K (Ysp p ρ j K)), hsum]
  exact ⟨_, inferInstance, basisOfLinearIndependentOfCardEqFinrank' bv hli hcard, jf,
    fun k => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']; exact (Module.finBasis K _ k.2).2⟩

/-- **(X) the twist scalar.** -/
theorem exists_twist_scalar {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρ ρ' : GQp p →* GL (Fin n) E) (c : GQp p → E)
    (hc : ∀ σ, matC p (ρ' σ : Matrix (Fin n) (Fin n) E) =
      algebraMap E ℂ_[p] (c σ) • matC p (ρ σ : Matrix (Fin n) (Fin n) E))
    (hc0 : ∀ σ, c σ ≠ 0) {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p]))
    (j : ι → ℤ) (hb : ∀ k, b k ∈ Ysp p ρ' (j k) E) {i₀ : ℤ} {y₀ : Fin n → ℂ_[p]}
    (hy₀ : y₀ ∈ Ysp p ρ i₀ E) (hne : y₀ ≠ 0) :
    ∃ (s : ℤ) (β : ℂ_[p]), β ≠ 0 ∧ ∀ σ ∈ E.fixingSubgroup,
      cpAct p σ β = (algebraMap E ℂ_[p] (c σ))⁻¹ * (cycPow p σ s • β) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, b.repr y₀ k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    have : b.repr y₀ = 0 := Finsupp.ext h
    simpa using congrArg b.repr.symm this
  refine ⟨j k - i₀, b.repr y₀ k, hk, fun σ hσ => ?_⟩
  have hcσ : algebraMap E ℂ_[p] (c σ) ≠ 0 := (map_ne_zero _).mpr (hc0 σ)
  set a := fun m => b.repr y₀ m
  have hy : y₀ = ∑ m, a m • b m := (b.sum_repr y₀).symm
  -- `(ρσ)ᵀ b_m = c⁻¹ χ^{j m} σ(b_m)`
  have hbm : ∀ m, (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (b m) =
      (algebraMap E ℂ_[p] (c σ))⁻¹ • (cycPow p σ (j m) • vAct p σ (b m)) := by
    intro m
    have h := hb m σ hσ
    rw [hc σ, Matrix.transpose_smul, Matrix.smul_mulVec] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hcσ, one_smul]
  have h1 : ∑ m, cpAct p σ (a m) • vAct p σ (b m) =
      ∑ m, ((algebraMap E ℂ_[p] (c σ))⁻¹ * (cycPow p σ (j m - i₀) • a m)) • vAct p σ (b m) := by
    have e1 : vAct p σ y₀ = ∑ m, cpAct p σ (a m) • vAct p σ (b m) := by
      conv_lhs => rw [hy]
      rw [vAct_sum]
      simp only [vAct_smul]
    rw [← e1, vAct_of_mem p hy₀ hσ]
    conv_lhs => rw [hy]
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.mulVec_smul, hbm m, sub_eq_add_neg, cycPow_add]
    ext t
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_mul]
    ring
  -- independence of `σ(b_m)`
  have hind : LinearIndependent ℂ_[p] fun m => vAct p σ (b m) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg m
    have h2 := congrArg (vAct p σ⁻¹) hg
    rw [vAct_sum, vAct_zero] at h2
    simp only [vAct_smul, vAct_vAct, inv_mul_cancel, vAct_one'] at h2
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h2 m
    have := congrArg (cpAct p σ) h3
    rwa [map_zero, ← cpAct_mul, mul_inv_cancel, cpAct_one] at this
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
  simp only [← sub_smul] at h1
  have := Fintype.linearIndependent_iff.mp hind _ h1 k
  exact sub_eq_zero.mp this

/-- **(M) multiplication by `β⁻¹`.** -/
theorem finrank_Ysp_twist {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρ ρ' : GQp p →* GL (Fin n) E) (c : GQp p → E)
    (hc : ∀ σ, matC p (ρ' σ : Matrix (Fin n) (Fin n) E) =
      algebraMap E ℂ_[p] (c σ) • matC p (ρ σ : Matrix (Fin n) (Fin n) E))
    (hc0 : ∀ σ, c σ ≠ 0) (s : ℤ) (β : ℂ_[p]) (hβ : β ≠ 0)
    (hrel : ∀ σ ∈ E.fixingSubgroup,
      cpAct p σ β = (algebraMap E ℂ_[p] (c σ))⁻¹ * (cycPow p σ s • β)) (i : ℤ) :
    Module.finrank E (Ysp p ρ i E) = Module.finrank E (Ysp p ρ' (i + s) E) := by
  have hcne : ∀ σ, algebraMap E ℂ_[p] (c σ) ≠ 0 := fun σ => (map_ne_zero _).mpr (hc0 σ)
  have hχ : ∀ σ, algebraMap ℚ_[p] ℂ_[p] (cycPow p σ s) ≠ 0 := by
    intro σ h
    have := cycPow_neg_mul p σ s
    rw [(map_eq_zero _).mp h, mul_zero] at this
    exact zero_ne_one this
  have hfwd : ∀ y ∈ Ysp p ρ i E, β⁻¹ • y ∈ Ysp p ρ' (i + s) E := by
    intro y hy σ hσ
    rw [hc σ, Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, hy σ hσ]
    ext m
    simp only [Pi.smul_apply, vAct, smul_eq_mul, map_mul, map_inv₀, hrel σ hσ]
    simp only [Algebra.smul_def, cycPow_add, map_mul]
    have := hχ σ
    have := hcne σ
    field_simp
  have hbwd : ∀ y ∈ Ysp p ρ' (i + s) E, β • y ∈ Ysp p ρ i E := by
    intro y hy σ hσ
    have h := hy σ hσ
    rw [hc σ, Matrix.transpose_smul, Matrix.smul_mulVec] at h
    have h' : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y =
        (algebraMap E ℂ_[p] (c σ))⁻¹ • (cycPow p σ (i + s) • vAct p σ y) := by
      rw [← h, smul_smul, inv_mul_cancel₀ (hcne σ), one_smul]
    rw [Matrix.mulVec_smul, h']
    ext m
    simp only [Pi.smul_apply, vAct, smul_eq_mul, map_mul, hrel σ hσ]
    simp only [Algebra.smul_def, cycPow_add, map_mul]
    have := hχ σ
    have := hcne σ
    field_simp
  let e : Ysp p ρ i E ≃ₗ[E] Ysp p ρ' (i + s) E :=
    { toFun := fun y => ⟨β⁻¹ • (y : Fin n → ℂ_[p]), hfwd y y.2⟩
      invFun := fun y => ⟨β • (y : Fin n → ℂ_[p]), hbwd y y.2⟩
      map_add' := fun y z => Subtype.ext (smul_add _ _ _)
      map_smul' := fun a y => by
        apply Subtype.ext
        show β⁻¹ • (a • (y : Fin n → ℂ_[p])) = a • (β⁻¹ • (y : Fin n → ℂ_[p]))
        rw [← algebraMap_smul (A := ℂ_[p]) a, ← algebraMap_smul (A := ℂ_[p]) a, smul_comm]
      left_inv := fun y => Subtype.ext (by
        show β • (β⁻¹ • (y : Fin n → ℂ_[p])) = y
        rw [smul_smul, mul_inv_cancel₀ hβ, one_smul])
      right_inv := fun y => Subtype.ext (by
        show β⁻¹ • (β • (y : Fin n → ℂ_[p])) = y
        rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]) }
  exact e.finrank_eq

end SenFinal

section SenAssembly

variable {n : ℕ}

theorem htMult_eq_finrank_Ysp (hT : TateTwistInvariants) (hA : AxSenTate)
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
    (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    htMult p ρ w = Module.finrank E (Ysp p ρ (-w) E) := by
  haveI : FiniteDimensional E (Ysp p ρ (-w) E) := Ysp_finiteDimensional p hT hA E ρ (-w)
  haveI : Module.Free E (Ysp p ρ (-w) E) := Module.Free.of_divisionRing _ _
  rw [htMult, finrank_htSpace_eq_Ysp p E hT hA ρ (-w),
    ← Module.finrank_mul_finrank ℚ_[p] E (Ysp p ρ (-w) E)]
  exact Nat.mul_div_cancel_left _ Module.finrank_pos

/-- **H-51, `SenTwist`, from Tate's two theorems.** -/
theorem senTwist_of_tate (hT : TateTwistInvariants) (hA : AxSenTate) : G0Galois.SenTwist := by
  intro p _ n ρ ρ' ψ S S' htw hS hS' hρ hρ'
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, ?_⟩
    rw [Multiset.card_eq_zero] at hS hS'
    simp [hS, hS']
  obtain ⟨E₁, hE₁, ρ₁, h₁, hw₁⟩ := hρ
  obtain ⟨E₂, hE₂, ρ₂, h₂, hw₂⟩ := hρ'
  let E₀ := E₁ ⊔ E₂
  let E := IntermediateField.normalClosure ℚ_[p] E₀ (PadicAlgCl p)
  haveI : FiniteDimensional ℚ_[p] E := inferInstance
  haveI : IsGalois ℚ_[p] E := IsGalois.mk
  have hE₀E : E₀ ≤ E := IntermediateField.le_normalClosure E₀
  let ρL := ρ.restrictLocal p
  let ρ'L := ρ'.restrictLocal p
  have hent₁ : ∀ σ i j, (((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j : E₁) : PadicAlgCl p) =
      (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro σ i j; rw [← h₁ σ]; rfl
  have hent₂ : ∀ σ i j, (((ρ₂ σ : Matrix (Fin n) (Fin n) E₂) i j : E₂) : PadicAlgCl p) =
      (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro σ i j; rw [← h₂ σ]; rfl
  have hmem : ∀ σ i j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E := by
    intro σ i j; rw [← hent₁]
    exact hE₀E ((le_sup_left : E₁ ≤ E₀) ((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j).2)
  have hmem' : ∀ σ i j, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E := by
    intro σ i j; rw [← hent₂]
    exact hE₀E ((le_sup_right : E₂ ≤ E₀) ((ρ₂ σ : Matrix (Fin n) (Fin n) E₂) i j).2)
  let ρE := liftGL E ρL hmem
  let ρ'E := liftGL E ρ'L hmem'
  have hwE : ∀ w, htMult p ρE w = S.count w := fun w =>
    (htMult_eq_of_lifts p ρL ρE ρ₁ (liftGL_map E ρL hmem) h₁ w).trans (hw₁ w)
  have hw'E : ∀ w, htMult p ρ'E w = S'.count w := fun w =>
    (htMult_eq_of_lifts p ρ'L ρ'E ρ₂ (liftGL_map E ρ'L hmem') h₂ w).trans (hw₂ w)
  -- the twist character with values in `E`
  have htwL : ∀ σ, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
      (ψ.toHom (decomp p σ) : PadicAlgCl p) • (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) :=
    fun σ => htw (decomp p σ)
  have hψmem : ∀ σ, (ψ.toHom (decomp p σ) : PadicAlgCl p) ∈ E := by
    intro σ
    have hdet : (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero _
    obtain ⟨j, hj⟩ : ∃ j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hdet (Matrix.det_eq_zero_of_row_eq_zero ⟨0, hn⟩ h)
    have e := congrFun (congrFun (htwL σ) ⟨0, hn⟩) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    have : (ψ.toHom (decomp p σ) : PadicAlgCl p) =
        (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j /
          (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j := by
      rw [e, mul_div_assoc, div_self hj, mul_one]
    rw [this]
    exact E.div_mem (hmem' σ _ _) (hmem σ _ _)
  let c : GQp p → E := fun σ => ⟨(ψ.toHom (decomp p σ) : PadicAlgCl p), hψmem σ⟩
  have hc0 : ∀ σ, c σ ≠ 0 := fun σ h =>
    (ψ.toHom (decomp p σ)).ne_zero (congrArg Subtype.val h)
  have hc : ∀ σ, matC p (ρ'E σ : Matrix (Fin n) (Fin n) E) =
      algebraMap E ℂ_[p] (c σ) • matC p (ρE σ : Matrix (Fin n) (Fin n) E) := by
    intro σ
    ext a b
    have hE : ((ρ'E σ : Matrix (Fin n) (Fin n) E) a b) = c σ * ((ρE σ : Matrix (Fin n) (Fin n) E) a b) :=
      Subtype.ext (by
        change (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) a b =
          (ψ.toHom (decomp p σ) : PadicAlgCl p) * (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) a b
        rw [htwL σ]
        rfl)
    simp only [matC, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hE, map_mul]
  -- dimensions of the `Y`'s
  have hdY : ∀ i, Module.finrank E (Ysp p ρE i E) = S.count (-i) := by
    intro i; rw [← hwE, htMult_eq_finrank_Ysp p hT hA E ρE (-i), neg_neg]
  have hdY' : ∀ i, Module.finrank E (Ysp p ρ'E i E) = S'.count (-i) := by
    intro i; rw [← hw'E, htMult_eq_finrank_Ysp p hT hA E ρ'E (-i), neg_neg]
  -- a basis of `ℂ_pⁿ` from the `Y_j(ρ')`
  let J' : Finset ℤ := (S'.map fun w => -w).toFinset
  have hsum : ∑ j ∈ J', Module.finrank E (Ysp p ρ'E j E) = n := by
    simp only [hdY']
    have hJ : J' = S'.toFinset.map ⟨fun w => -w, neg_injective⟩ := by
      ext j; simp [J']
    rw [hJ, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, neg_neg]
    rw [Multiset.toFinset_sum_count_eq, hS']
  obtain ⟨ι, _, b, jb, hb⟩ := exists_basis_Ysp p hT hA E ρ'E J' hsum
  -- a nonzero vector in some `Y_{i₀}(ρ)`
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∈ S := by
    have : S ≠ 0 := by
      intro h; rw [h, Multiset.card_zero] at hS; omega
    exact Multiset.exists_mem_of_ne_zero this
  haveI : FiniteDimensional E (Ysp p ρE (-w₀) E) := Ysp_finiteDimensional p hT hA E ρE (-w₀)
  have hne : Ysp p ρE (-w₀) E ≠ ⊥ := by
    intro h
    have := hdY (-w₀)
    rw [h, finrank_bot, neg_neg] at this
    exact (Multiset.count_ne_zero.mpr hw₀) this.symm
  obtain ⟨y₀, hy₀, hy₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨s, β, hβ, hrel⟩ := exists_twist_scalar p ρE ρ'E c hc hc0 b jb hb hy₀ hy₀ne
  have hdim : ∀ i, Module.finrank E (Ysp p ρE i E) = Module.finrank E (Ysp p ρ'E (i + s) E) :=
    finrank_Ysp_twist p ρE ρ'E c hc hc0 s β hβ hrel
  refine ⟨-s, ?_⟩
  ext u
  have e1 : S.count (u + s) = S'.count u := by
    have := hdim (-(u + s))
    rw [hdY, hdY', neg_neg] at this
    rw [this]
    congr 1
    ring
  have e2 : (S.map (· + -s)).count u = S.count (u + s) := by
    have := Multiset.count_map_eq_count' (fun w => w + -s) S (add_left_injective _) (u + s)
    simp only [add_neg_cancel_right] at this
    exact this
  rw [e2, e1]

end SenAssembly

/-! ## §13. Glue proved: `AttachedConj` (Chebotarev with Brauer–Nesbitt)

From the kernel's proved leaves T18 (`ZInQ.Contrib.frobeniusDense`, through Tau Ceti's Chebotarev)
and T19 (`TSkolemKW.C10.brauerNesbittChar0'`), via `C9Rhof.iso_of_arithFrob`
(`ZInQKernel/HDecomp/ModCurves/C9.lean`). The bridge: pkg-I4's matrix-valued `GaloisRep` as a
Mathlib `Representation` on `ℚ̄_ℓ²`; its `IsSemisimple` (invariant complements) as
`IsSemisimpleModule` over the group algebra (Mathlib's `Representation.mapSubmodule`). -/

section AttachedConjSec


variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- pkg-I4's `GaloisRep` as a Mathlib `Representation` on `ℚ̄_ℓⁿ`. -/
def galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Representation (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ (Fin n → PadicAlgCl ℓ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
    ((Units.coeHom _).comp ρ.toHom)

theorem galRepRep_apply {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    galRepRep ρ σ = Matrix.toLin' (ρ.mat σ) := rfl

theorem toMatrix_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (galRepRep ρ σ) = ρ.mat σ := by
  rw [LinearMap.toMatrix_eq_toMatrix', galRepRep_apply, LinearMap.toMatrix'_toLin']

theorem trace_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ σ) = (ρ.mat σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace (PadicAlgCl ℓ) (Pi.basisFun (PadicAlgCl ℓ) (Fin n)),
    toMatrix_galRepRep]

theorem continuous_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Continuous fun g => LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (galRepRep ρ g) := by
  simp only [toMatrix_galRepRep]
  exact Units.continuous_val.comp ρ.continuous_toHom

theorem mem_invtSubmodule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n)
    (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)) :
    W ∈ (galRepRep ρ).invtSubmodule ↔ ∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
  rw [Representation.mem_invtSubmodule]
  refine forall_congr' fun σ => ?_
  rw [Module.End.mem_invtSubmodule, Submodule.map_le_iff_le_comap, galRepRep_apply]

theorem isSemisimpleModule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (h : ZInQ.Contrib.G9.PkgI4.GaloisRep.IsSemisimple ρ) :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ) (galRepRep ρ).asModule := by
  rw [isSemisimpleModule_iff, ← (galRepRep ρ).mapSubmodule.complementedLattice_iff]
  refine ⟨fun a => ?_⟩
  obtain ⟨W, hW⟩ := a
  obtain ⟨W', hc, hW'⟩ := h W ((mem_invtSubmodule_galRepRep ρ W).mp hW)
  refine ⟨⟨W', (mem_invtSubmodule_galRepRep ρ W').mpr hW'⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subtype.ext hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subtype.ext hc.sup_eq_top

/-- `C9Rhof.FrobeniusDense` from the kernel's proved T18 (same body, other namespace). -/
theorem frobeniusDense_C9 : C9Rhof.FrobeniusDense := by
  intro U hU σ S
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := ZInQ.Contrib.frobeniusDense U hU σ S
  exact ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩

/-- **`AttachedConj`, proved** (from T18, T19 in the kernel). -/
theorem attachedConj_proof : AttachedConj := by
  intro ℓ _ ρ ρ' S hss hss' hS
  have htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (τ : ZInQ.Contrib.G9.PkgI4.GQ),
      ZInQ.Contrib.G9.PkgI4.LiesOver v p → ZInQ.Contrib.G9.PkgI4.IsArithFrob τ v p →
      LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ τ) =
        LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ' τ) := by
    intro p hp hpS v τ hv hτ
    rw [trace_galRepRep, trace_galRepRep]
    exact (hS p hp hpS).2.2 v τ hv hτ
  obtain ⟨e⟩ := C9Rhof.iso_of_arithFrob TSkolemKW.C10.brauerNesbittChar0' frobeniusDense_C9 S
    (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (galRepRep ρ) (galRepRep ρ') (continuous_galRepRep ρ) (continuous_galRepRep ρ')
    (isSemisimpleModule_galRepRep ρ hss) (isSemisimpleModule_galRepRep ρ' hss') htr
  let L : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    ((galRepRep ρ).asModuleEquiv.symm.trans (e.restrictScalars (PadicAlgCl ℓ))).trans
      (galRepRep ρ').asModuleEquiv
  have hL : ∀ σ v, L (galRepRep ρ σ v) = galRepRep ρ' σ (L v) := by
    intro σ v
    simp only [L, LinearEquiv.trans_apply, Representation.asModuleEquiv_symm_map_rho,
      LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  let M := LinearMap.toMatrix' L.toLinearMap
  let M' := LinearMap.toMatrix' L.symm.toLinearMap
  have h1 : M' * M = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.symm.toLinearMap ∘ₗ L.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.symm_apply_apply v, LinearMap.toMatrix'_id]
  have h2 : M * M' = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.toLinearMap ∘ₗ L.symm.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.apply_symm_apply v, LinearMap.toMatrix'_id]
  have hcomm : ∀ σ, M * ρ.mat σ = ρ'.mat σ * M := by
    intro σ
    have : L.toLinearMap ∘ₗ galRepRep ρ σ = galRepRep ρ' σ ∘ₗ L.toLinearMap :=
      LinearMap.ext fun v => hL σ v
    have h' := congrArg LinearMap.toMatrix' this
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, galRepRep_apply, galRepRep_apply,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at h'
    exact h'
  refine ⟨⟨M', M, h1, h2⟩, fun σ => Units.ext ?_⟩
  change ρ.mat σ = M' * ρ'.mat σ * M
  rw [mul_assoc, ← hcomm σ, ← mul_assoc, h1, one_mul]

end AttachedConjSec


/-! ## §17. `DetFromFrobenius` (R14 glue), proved

From the kernel's T18 (density of arithmetic Frobenius elements), Mathlib's cyclotomic characters
(`cyclotomicCharacter`, `modularCyclotomicCharacter`, `cyclotomicCharacter.continuous`) and an
elementary lemma: an arithmetic Frobenius at `v ∣ p` raises roots of unity of order prime to `p`
to the `p`-th power (`arithFrob_pow_of_rootOfUnity`). -/

section DetFrob

open ZInQ.Contrib.G9.PkgI4


theorem val_eq_one_of_pow {v : ValuationSubring Qbar} {x : Qbar} {m : ℕ} (hm : m ≠ 0)
    (hx : x ^ m = 1) : v.valuation x = 1 := by
  have h := congrArg v.valuation hx
  rw [map_pow, map_one] at h
  rcases lt_trichotomy (v.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le h1 hm))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hm))

/-- An arithmetic Frobenius at `v ∣ p` acts on roots of unity of order prime to `p` as `ζ ↦ ζ^p`. -/
theorem arithFrob_pow_of_rootOfUnity {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hv : LiesOver v p) (hσ : IsArithFrob σ v p) {ζ : Qbar} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1)
    (hpm : ¬ p ∣ m) : σ ζ = ζ ^ p := by
  set val := v.valuation
  have hζ1 : val ζ = 1 := val_eq_one_of_pow hm hζ
  have hζv : ζ ∈ v := (v.valuation_le_one_iff ζ).mp hζ1.le
  have hσζm : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  have hσζ1 : val (σ ζ) = 1 := val_eq_one_of_pow hm hσζm
  have hζp0 : ζ ^ p ≠ 0 := pow_ne_zero _ (by rintro rfl; simp [hm] at hζ)
  set ξ := σ ζ / ζ ^ p with hξ
  have hξm : ξ ^ m = 1 := by
    rw [hξ, div_pow, hσζm, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
  have hlt : val (σ ζ - ζ ^ p) < 1 := (v.mem_nonunits_iff).mp (hσ.2 ζ hζv)
  have hξ1 : val (ξ - 1) < 1 := by
    have : ξ - 1 = (σ ζ - ζ ^ p) / ζ ^ p := by rw [hξ]; field_simp
    rw [this, map_div₀, map_pow, hζ1, one_pow, div_one]
    exact hlt
  by_contra hne
  have hξne : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ, div_eq_one_iff_eq hζp0] at h
    exact h
  -- `Σ_{j<m} ξ^j = 0`
  have hgeom : ∑ j ∈ Finset.range m, ξ ^ j = 0 := by
    have := geom_sum_mul ξ m
    rw [hξm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hξne)
  -- each `ξ^j - 1` is in the maximal ideal
  have hj : ∀ j, val (ξ ^ j - 1) < 1 := by
    intro j
    have : ξ ^ j - 1 = (ξ - 1) * ∑ i ∈ Finset.range j, ξ ^ i := by
      rw [mul_comm, geom_sum_mul]
    rw [this, map_mul]
    have hs : val (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 := by
      apply Valuation.map_sum_le
      intro i _
      rw [map_pow]
      have : val ξ = 1 := val_eq_one_of_pow hm hξm
      rw [this, one_pow]
    calc val (ξ - 1) * val (∑ i ∈ Finset.range j, ξ ^ i) ≤ val (ξ - 1) * 1 :=
          mul_le_mul_of_nonneg_left hs zero_le
      _ < 1 := by rw [mul_one]; exact hξ1
  -- so `m ∈` the maximal ideal
  have hmval : val (m : Qbar) < 1 := by
    have : (m : Qbar) = -∑ j ∈ Finset.range m, (ξ ^ j - 1) := by
      rw [Finset.sum_sub_distrib, hgeom]; simp
    rw [this, Valuation.map_neg]
    exact Valuation.map_sum_lt' _ zero_lt_one fun j _ => hj j
  have hpval : val (p : Qbar) < 1 := (v.mem_nonunits_iff).mp hv
  -- `gcd(m, p) = 1` gives `1` in the maximal ideal
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * p = 1 := by
    have := Nat.Coprime.isCoprime hcop.symm
    obtain ⟨a, b, h⟩ := this
    exact ⟨a, b, by exact_mod_cast h⟩
  have h1 : val (1 : Qbar) < 1 := by
    have : (1 : Qbar) = (a : Qbar) * m + (b : Qbar) * p := by exact_mod_cast hab.symm
    rw [this]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v a⟩))
        hmval
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v b⟩))
        hpval
  rw [map_one] at h1
  exact lt_irrefl _ h1

end DetFrob

section DetFrob2

open ZInQ.Contrib.G9.PkgI4

theorem pow_eq_pow_mod_of {M : Type*} [Monoid M] {t : M} {n : ℕ} (ht : t ^ n = 1) (a : ℕ) :
    t ^ a = t ^ (a % n) := by
  conv_lhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, ht, one_pow, mul_one]

/-- The cyclotomic character at an arithmetic Frobenius at `p ≠ ℓ` is `p`. -/
theorem cyc_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (p : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  have hl : (ℓ ^ n) ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  haveI : NeZero (ℓ ^ n) := ⟨hl⟩
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ (ℓ ^ n) = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hpm : ¬ p ∣ ℓ ^ n := fun h =>
    hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h))
  change σ (t : Qbar) = ((t ^ ((p : ZMod (ℓ ^ n))).val : Qbarˣ) : Qbar)
  rw [arithFrob_pow_of_rootOfUnity hp hv hσ hl htn hpm, Units.val_pow_eq_pow_val, ZMod.val_natCast,
    ← pow_eq_pow_mod_of htn]

/-- The cyclotomic character mod `N` at an arithmetic Frobenius at `p ∤ N` is `p`. -/
theorem modCyc_arithFrob {N : ℕ} [NeZero N] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((modularCyclotomicCharacter Qbar (HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N)
      σ.toRingEquiv : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := by
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ N = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  change σ (t : Qbar) = ((t ^ ((p : ZMod N)).val : Qbarˣ) : Qbar)
  rw [arithFrob_pow_of_rootOfUnity hp hv hσ (NeZero.ne N) htn hpN, Units.val_pow_eq_pow_val,
    ZMod.val_natCast, ← pow_eq_pow_mod_of htn]

end DetFrob2

section EpsZero

open ZInQ.Contrib.G9.PkgI4

variable {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
  {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- `ιC` on `m`-th roots of unity is a bijection `μ_m(ℚ̄) ≃ μ_m(ℂ)`. -/
noncomputable def rootsEquiv (m : ℕ) [NeZero m] : rootsOfUnity m Qbar ≃* rootsOfUnity m ℂ :=
  MulEquiv.ofBijective (restrictRootsOfUnity ιC m) <| by
    have hinj : Function.Injective (restrictRootsOfUnity ιC m) := by
      intro x y h
      apply Subtype.ext; apply Units.ext
      have := congrArg (fun z : rootsOfUnity m ℂ => ((z : ℂˣ) : ℂ)) h
      simp only [restrictRootsOfUnity_coe_apply] at this
      exact ιC.toRingHom.injective this
    refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar m, Complex.card_rootsOfUnity]

theorem iotaC_rootsEquiv_symm (m : ℕ) [NeZero m] (x : rootsOfUnity m ℂ) :
    ιC (((rootsEquiv ιC m).symm x : Qbarˣ) : Qbar) = ((x : ℂˣ) : ℂ) := by
  have h := (rootsEquiv ιC m).apply_symm_apply x
  conv_rhs => rw [← h]
  rfl

/-- The order of every value of `χ` divides `m = #(ℤ/N)ˣ`. -/
noncomputable def chiRoots : (ZMod N)ˣ →* rootsOfUnity (Nat.card (ZMod N)ˣ) ℂ :=
  MonoidHom.codRestrict χ.toUnitHom _ fun u => by
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]

/-- The nebentypus as an `ℓ`-adic character of `(ℤ/N)ˣ`: `u ↦ ιL(ιC⁻¹(χ u))`. -/
noncomputable def chiL : (ZMod N)ˣ →* (PadicAlgCl ℓ)ˣ :=
  haveI : NeZero (Nat.card (ZMod N)ˣ) := ⟨Nat.card_pos.ne'⟩
  (Units.map ιL.toMonoidHom).comp ((rootsOfUnity (Nat.card (ZMod N)ˣ) Qbar).subtype.comp
    ((rootsEquiv ιC (Nat.card (ZMod N)ˣ)).symm.toMonoidHom.comp (chiRoots χ)))

theorem chiL_spec (u : (ZMod N)ˣ) : ∃ γ : Qbar, ιC γ = χ (u : ZMod N) ∧
    ((chiL ιC ιL χ u : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  haveI : NeZero (Nat.card (ZMod N)ˣ) := ⟨Nat.card_pos.ne'⟩
  refine ⟨(((rootsEquiv ιC (Nat.card (ZMod N)ˣ)).symm (chiRoots χ u) : Qbarˣ) : Qbar), ?_, rfl⟩
  rw [iotaC_rootsEquiv_symm]
  rfl

/-- The cyclotomic character mod `N` on `G_ℚ`. -/
noncomputable def modCycQ : GQ →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Qbar (HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N)).comp
    G0Galois.toRingEquivQ

/-- `ε₀ = chiL ∘ modCycQ`: the nebentypus as a Galois character. -/
noncomputable def eps0 : GQ →* (PadicAlgCl ℓ)ˣ := (chiL ιC ιL χ).comp modCycQ

theorem eps0_finite : (Set.range (eps0 ιC ιL χ)).Finite :=
  (Set.finite_range (chiL ιC ιL χ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)

theorem eps0_arithFrob {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ∃ γ : Qbar, ιC γ = χ (p : ZMod N) ∧ ((eps0 ιC ιL χ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  obtain ⟨γ, hγ, hval⟩ := chiL_spec ιC ιL χ (modCycQ σ)
  refine ⟨γ, ?_, hval⟩
  rw [hγ]
  congr 1
  exact modCyc_arithFrob hp hpN hv hσ

/-- `ε₀` is trivial on `Gal(ℚ̄/ℚ(μ_N))`, an open subgroup; hence continuous. -/
theorem eps0_continuous : Continuous (eps0 ιC ιL χ) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar N
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hK : ∀ σ ∈ K.fixingSubgroup, eps0 ιC ιL χ σ = 1 := by
    intro σ hσ
    have hfix : σ ζ = ζ := hσ ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
    have h1 : modCycQ (N := N) σ = 1 := by
      apply Units.ext
      refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
      have htn : (t : Qbar) ^ N = 1 := by
        have := (mem_rootsOfUnity _ _).mp ht
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one htn
      change σ (t : Qbar) = ((t ^ ((1 : (ZMod N)ˣ) : ZMod N).val : Qbarˣ) : Qbar)
      rw [← hi, map_pow, hfix, Units.val_pow_eq_pow_val, ← hi]
      by_cases hN1 : N = 1
      · subst hN1
        have : (t : Qbar) = 1 := by simpa using htn
        rw [hi, this, one_pow]
      · haveI : Fact (1 < N) := ⟨by have := NeZero.ne N; omega⟩
        rw [Units.val_one, ZMod.val_one, pow_one]
    simp [eps0, h1]
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  have hnhds : (K.fixingSubgroup : Set GQ) ∈ nhds (1 : GQ) :=
    (IntermediateField.fixingSubgroup_isOpen K).mem_nhds K.fixingSubgroup.one_mem
  exact tendsto_nhds_of_eventually_eq (Filter.mem_of_superset hnhds fun σ hσ => hK σ hσ)

end EpsZero


section DetFrobMain

open ZInQ.Contrib.G9.PkgI4

theorem toRingEquivQ_eq : G0Galois.toRingEquivQ = MulSemiringAction.toRingAut Gal(Qbar/ℚ) Qbar := by
  ext σ x; rfl

theorem continuous_units_map {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
    [TopologicalSpace N] {X : Type*} [TopologicalSpace X] (f : M →* N) (hf : Continuous f)
    {c : X → Mˣ} (hc : Continuous c) : Continuous fun x => Units.map f (c x) := by
  rw [Units.continuous_iff]
  exact ⟨hf.comp (Units.continuous_val.comp hc), hf.comp (Units.continuous_coe_inv.comp hc)⟩

theorem continuous_cycQ (ℓ : ℕ) [Fact ℓ.Prime] : Continuous (G0Galois.cycQ ℓ) := by
  have h := cyclotomicCharacter.continuous ℓ ℚ Qbar
  rw [← toRingEquivQ_eq] at h
  have hf : Continuous ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom) :=
    (continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val
  exact continuous_units_map _ hf h

theorem cycQ_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((G0Galois.cycQ ℓ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (p : PadicAlgCl ℓ) := by
  change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
    (((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [cyc_arithFrob hp hpl hv hσ]
  simp

/-- **`DetFromFrobenius`, proved** (from the kernel's T18 and Mathlib's cyclotomic characters). -/
theorem detFromFrobenius_proof : DetFromFrobenius := by
  intro ℓ _ ιC ιL N k χ ρ hN hfrob
  haveI : NeZero N := ⟨hN.ne'⟩
  let detU : GQ →* (PadicAlgCl ℓ)ˣ := Matrix.GeneralLinearGroup.det.comp ρ.toHom
  have hdetU : ∀ σ, ((detU σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (ρ.mat σ).det := fun σ => rfl
  have hdetc : Continuous detU := by
    rw [Units.continuous_iff]
    refine ⟨(Units.continuous_val.comp ρ.continuous_toHom).matrix_det, ?_⟩
    have : (fun σ => (((detU σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)) =
        fun σ => (((ρ.toHom σ)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) _).det := by
      funext σ; rfl
    rw [this]
    exact (Units.continuous_coe_inv.comp ρ.continuous_toHom).matrix_det
  let δ : GQ → (PadicAlgCl ℓ)ˣ := fun σ => detU σ * G0Galois.cycQ ℓ σ ^ (-(k - 1))
  have hδc : Continuous δ := hdetc.mul ((continuous_cycQ ℓ).zpow _)
  have hp0 : ∀ p : ℕ, p.Prime → (p : PadicAlgCl ℓ) ≠ 0 := fun p hp => by
    exact_mod_cast hp.ne_zero
  have hEq : δ = eps0 ιC ιL χ := by
    refine C9Rhof.eq_of_eq_on_arithFrob frobeniusDense_C9 (N * ℓ).primeFactors δ (eps0 ιC ιL χ)
      hδc (eps0_continuous ιC ιL χ) fun p hp hpS v τ hv hτ => ?_
    have hNl : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
    have hpNl : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hNl⟩)
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    have hpl : p ≠ ℓ := fun h => hpNl (h ▸ Dvd.intro_left N rfl)
    obtain ⟨-, β, hβ, hdet⟩ := hfrob p hp hpNl
    obtain ⟨γ, hγ, hε⟩ := eps0_arithFrob ιC ιL χ hp hpN hv hτ
    have hβγ : β = γ * (p : Qbar) ^ (k - 1) := by
      apply ιC.toRingHom.injective
      change ιC β = ιC (γ * (p : Qbar) ^ (k - 1))
      rw [hβ, map_mul, map_zpow₀, map_natCast ιC, hγ]
    apply Units.ext
    change (detU τ : PadicAlgCl ℓ) * ((G0Galois.cycQ ℓ τ ^ (-(k - 1)) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = _
    rw [hdetU, hdet v τ hv hτ, Units.val_zpow_eq_zpow_val, cycQ_arithFrob hp hpl hv hτ, hε, hβγ,
      map_mul, map_zpow₀, map_natCast ιL, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (hp0 p hp)),
      mul_one]
  refine ⟨eps0 ιC ιL χ, eps0_finite ιC ιL χ, fun σ => ?_⟩
  rw [← hEq]
  change (ρ.mat σ).det = ((detU σ * G0Galois.cycQ ℓ σ ^ (-(k - 1)) * G0Galois.cycQ ℓ σ ^ (k - 1) :
    (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)
  rw [zpow_neg, inv_mul_cancel_right, hdetU]

end DetFrobMain


section ArtinHelpers

open ZInQ.Contrib.G9.PkgI4

/-- A root of unity in `ℂ` is `ιC` of an element of `ℚ̄`. -/
theorem mem_range_of_pow_eq_one (ιC : Qbar →ₐ[ℚ] ℂ) {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    z ∈ Set.range ιC := by
  haveI : NeZero n := ⟨hn⟩
  have hz0 : z ≠ 0 := by rintro rfl; simp [hn] at hz
  let u : rootsOfUnity n ℂ := ⟨Units.mk0 z hz0, by
    rw [mem_rootsOfUnity]; apply Units.ext; simp [hz]⟩
  refine ⟨(((rootsEquiv ιC n).symm u : Qbarˣ) : Qbar), ?_⟩
  rw [iotaC_rootsEquiv_symm]
  rfl

/-- The trace of a complex `2 × 2` matrix of finite order is `ιC` of an algebraic number. -/
theorem trace_mem_range_of_pow_eq_one (ιC : Qbar →ₐ[ℚ] ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ}
    (hn : n ≠ 0) (hM : M ^ n = 1) : M.trace ∈ ιC.range := by
  rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine Subalgebra.multiset_sum_mem _ fun r hr => ?_
  have hroot : M.charpoly.IsRoot r := (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp hr
  have hspec : r ∈ spectrum ℂ M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  have hpow : r ^ n ∈ spectrum ℂ (M ^ n) := spectrum.pow_mem_pow M n hspec
  rw [hM, spectrum.one_eq, Set.mem_singleton_iff] at hpow
  obtain ⟨a, ha⟩ := mem_range_of_pow_eq_one ιC hn hpow
  exact ⟨a, ha⟩

end ArtinHelpers


section ArtinHelpers2

open ZInQ.Contrib.G9.PkgI4

/-- The subring of `ℂ` generated by `ιC(ℚ̄)` and a finite set `E`. -/
noncomputable def genRing (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) : Subring ℂ :=
  (MvPolynomial.eval₂Hom (ιC : Qbar →+* ℂ) (fun e : E => (e : ℂ))).range

theorem mem_genRing_of_mem (ιC : Qbar →ₐ[ℚ] ℂ) {E : Set ℂ} {e : ℂ} (he : e ∈ E) :
    e ∈ genRing ιC E :=
  ⟨MvPolynomial.X ⟨e, he⟩, by simp⟩

theorem iotaC_mem_genRing (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) (a : Qbar) : ιC a ∈ genRing ιC E :=
  ⟨MvPolynomial.C a, by simp⟩

/-- **Specialization (Hilbert's Nullstellensatz).** A ring map `genRing ιC E → ℚ̄` that is `ιC⁻¹`
on `ιC(ℚ̄)`. -/
theorem exists_specialization (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) [Finite E] :
    ∃ φ : genRing ιC E →+* Qbar, ∀ a : Qbar, φ ⟨ιC a, iotaC_mem_genRing ιC E a⟩ = a := by
  classical
  let F := MvPolynomial.eval₂Hom (ιC : Qbar →+* ℂ) (fun e : E => (e : ℂ))
  have hI : RingHom.ker F ≠ ⊤ := by
    intro h
    have : (1 : MvPolynomial E Qbar) ∈ RingHom.ker F := h ▸ Submodule.mem_top
    simp [RingHom.mem_ker] at this
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal Qbar hm
  let ev : MvPolynomial E Qbar →+* Qbar := MvPolynomial.eval x
  have hle : RingHom.ker F.rangeRestrict ≤ RingHom.ker ev := by
    rw [RingHom.ker_rangeRestrict]
    intro f hf
    have hfm : f ∈ m := hIm hf
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfm
    rw [RingHom.mem_ker]
    exact hfm
  let e := RingHom.quotientKerEquivOfSurjective (F.rangeRestrict_surjective)
  refine ⟨(Ideal.Quotient.lift _ ev (fun a ha => RingHom.mem_ker.mp (hle ha))).comp e.symm.toRingHom, fun a => ?_⟩
  have h1 : (⟨ιC a, iotaC_mem_genRing ιC E a⟩ : genRing ιC E) = F.rangeRestrict (MvPolynomial.C a) := by
    apply Subtype.ext; simp [F]
  rw [h1]
  change Ideal.Quotient.lift _ ev (fun a ha => RingHom.mem_ker.mp (hle ha)) (e.symm (F.rangeRestrict (MvPolynomial.C a))) = a
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  simp [ev]

/-- A homomorphism to `GL_n(ℂ)` with entries in a subring `A` lifts to `GL_n(A)`. -/
def liftGLSub {G : Type*} [Group G] {n : ℕ} (A : Subring ℂ) (f : G →* GL (Fin n) ℂ)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) ℂ) i j ∈ A) : G →* GL (Fin n) A :=
  let M : G → Matrix (Fin n) (Fin n) A := fun g i j => ⟨(f g : Matrix (Fin n) (Fin n) ℂ) i j, h g i j⟩
  have hM : ∀ g, (M g).map A.subtype = (f g : Matrix (Fin n) (Fin n) ℂ) := fun g => by ext i j; rfl
  have hinj : Function.Injective (fun B : Matrix (Fin n) (Fin n) A => B.map A.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hmul : ∀ g g', M (g * g') = M g * M g' := fun g g' => hinj (by
    simp only [Matrix.map_mul, hM, map_mul, Units.val_mul])
  have hone : M 1 = 1 := hinj (by simp only [hM, map_one, Units.val_one, Matrix.map_one,
    map_zero, map_one])
  { toFun := fun g => ⟨M g, M g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
      by rw [← hmul, inv_mul_cancel, hone]⟩
    map_one' := Units.ext hone
    map_mul' := fun g g' => Units.ext (hmul g g') }

theorem liftGLSub_coe {G : Type*} [Group G] {n : ℕ} (A : Subring ℂ) (f : G →* GL (Fin n) ℂ)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) ℂ) i j ∈ A) (g : G) (i j : Fin n) :
    (((liftGLSub A f h g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j : ℂ) =
      (f g : Matrix (Fin n) (Fin n) ℂ) i j := rfl

/-- **Maschke.** A `GaloisRep` with finite image is semisimple. -/
theorem isSemisimple_of_finite_range {ℓ n : ℕ} [Fact ℓ.Prime] (ρ : GaloisRep ℓ n)
    (h : (Set.range ρ.toHom).Finite) : ρ.IsSemisimple := by
  classical
  let H := ρ.toHom.range
  haveI : Finite H := by
    have : (H : Set (GL (Fin n) (PadicAlgCl ℓ))) = Set.range ρ.toHom := MonoidHom.coe_range _
    exact Set.Finite.to_subtype (this ▸ h)
  haveI : NeZero (Nat.card H : PadicAlgCl ℓ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let ρH : Representation (PadicAlgCl ℓ) H (Fin n → PadicAlgCl ℓ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
      ((Units.coeHom _).comp H.subtype)
  have hρH : ∀ (x : H), ρH x = Matrix.toLin' ((x : GL (Fin n) (PadicAlgCl ℓ)) :
      Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := fun _ => rfl
  have hss : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) H) ρH.asModule := inferInstance
  rw [isSemisimpleModule_iff, ← ρH.mapSubmodule.complementedLattice_iff] at hss
  have hmem : ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
      W ∈ ρH.invtSubmodule ↔ ∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
    intro W
    rw [Representation.mem_invtSubmodule]
    constructor
    · intro hW σ
      have := hW ⟨ρ.toHom σ, σ, rfl⟩
      rw [Module.End.mem_invtSubmodule, hρH] at this
      rw [Submodule.map_le_iff_le_comap]
      exact this
    · rintro hW ⟨_, σ, rfl⟩
      rw [Module.End.mem_invtSubmodule, hρH, ← Submodule.map_le_iff_le_comap]
      exact hW σ
  intro W hW
  obtain ⟨b, hb⟩ := hss.exists_isCompl ⟨W, (hmem W).mpr hW⟩
  refine ⟨b.1, ⟨?_, ?_⟩, (hmem b.1).mp b.2⟩
  · rw [disjoint_iff]
    exact congrArg Subtype.val hb.inf_eq_bot
  · rw [codisjoint_iff]
    exact congrArg Subtype.val hb.sup_eq_top

/-- Every prime `p` has an arithmetic Frobenius (from the kernel's Chebotarev files). -/
theorem exists_arithFrob (p : ℕ) (hp : p.Prime) :
    ∃ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p ∧ IsArithFrob τ v p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := ZInQ.Contrib.ChebFD.C10.Zbar)
    (Ideal.span {(p : ℤ)}) ⊥ (by simp)
  obtain ⟨h, hh⟩ := ZInQ.Contrib.ChebFD.C10.frobExistsAt_of_finite
    ZInQ.Contrib.ChebFD.C10.frobExistsFinite p P hPp
  obtain ⟨hv, hτ⟩ := ZInQ.Contrib.ChebFD.HSyn.liesOver_and_isArithFrob P h p hp hPp hh
  exact ⟨_, h, hv, hτ⟩

end ArtinHelpers2


section ArtinMain

open ZInQ.Contrib.G9.PkgI4

/-- **`ArtinTransport`, proved**: specialize the entries of Deligne–Serre's `ρ_f` to `ℚ̄`
(Nullstellensatz, identity on `ιC(ℚ̄)`), apply `ιL`; semisimple by Maschke; `ε = det`. -/
theorem artinTransport_proof : ArtinTransport := by
  intro hDS ℓ _ ιC ιL N χ g hN hg
  classical
  obtain ⟨ρc, hcont, hfin, hloc⟩ := hDS N χ g hN hg
  let E : Set ℂ := ⋃ M ∈ Set.range ρc,
    Set.range fun ij : Fin 2 × Fin 2 => (M : Matrix (Fin 2) (Fin 2) ℂ) ij.1 ij.2
  haveI : Finite E := (hfin.biUnion fun M _ => Set.finite_range _).to_subtype
  have hmem : ∀ σ i j, (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j ∈ genRing ιC E := fun σ i j =>
    mem_genRing_of_mem ιC (Set.mem_biUnion (Set.mem_range_self σ) ⟨(i, j), rfl⟩)
  obtain ⟨φ, hφ⟩ := exists_specialization ιC E
  let ρA := liftGLSub (genRing ιC E) ρc hmem
  let g' : genRing ιC E →+* PadicAlgCl ℓ := ιL.toRingHom.comp φ
  let ρh : GQ →* GL (Fin 2) (PadicAlgCl ℓ) := (Matrix.GeneralLinearGroup.map g').comp ρA
  have hentry : ∀ σ i j, (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j =
      g' ⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ := fun _ _ _ => rfl
  have hker : ∀ σ, ρc σ = 1 → ρh σ = 1 := by
    intro σ h
    apply Units.ext
    ext i j
    rw [hentry]
    have hval : (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = if i = j then 1 else 0 := by
      rw [h, Units.val_one, Matrix.one_apply]
    by_cases hij : i = j
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 1 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 1; rw [hval, if_pos hij])
      rw [this, map_one, Units.val_one, Matrix.one_apply, if_pos hij]
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 0 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 0; rw [hval, if_neg hij])
      rw [this, map_zero, Units.val_one, Matrix.one_apply, if_neg hij]
  have hopen : IsOpen (ρc.ker : Set GQ) := by
    have hcl : IsClosed (ρc.ker : Set GQ) := by
      have : (ρc.ker : Set GQ) = ρc ⁻¹' {1} := by ext; simp
      rw [this]; exact isClosed_singleton.preimage hcont
    haveI : Finite ρc.range := by
      have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
      exact Set.Finite.to_subtype (this ▸ hfin)
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hρhc : Continuous ρh := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    exact tendsto_nhds_of_eventually_eq
      (Filter.mem_of_superset (hopen.mem_nhds ρc.ker.one_mem) fun σ hσ => hker σ hσ)
  have hdep : ∀ σ σ', ρc σ = ρc σ' → ρh σ = ρh σ' := by
    intro σ σ' h
    have h1 : ρc (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hρfin : (Set.range ρh).Finite := by
    refine (hfin.image fun M => ρh (Function.invFun ρc M)).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine ⟨ρc σ, ⟨σ, rfl⟩, hdep _ _ ?_⟩
    exact Function.invFun_eq ⟨σ, rfl⟩
  let ρ : GaloisRep ℓ 2 := ⟨ρh, hρhc⟩
  refine ⟨ρ, isSemisimple_of_finite_range ρ hρfin, ?_, ?_⟩
  · intro p hp hpNl
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    obtain ⟨hun, hfr⟩ := hloc p hp hpN
    refine ⟨fun v hv σ hσ => hker _ (hun v hv σ hσ), ?_⟩
    obtain ⟨v₀, τ₀, hv₀, hτ₀⟩ := exists_arithFrob p hp
    have htr₀ := (hfr v₀ τ₀ hv₀ hτ₀).1
    -- `ρc τ₀` has finite order
    haveI : Finite ρc.range := by
      have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
      exact Set.Finite.to_subtype (this ▸ hfin)
    let x : ρc.range := ⟨ρc τ₀, τ₀, rfl⟩
    have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
    have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
    have hpow : (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ) ^ orderOf x = 1 := by
      have h1 := congrArg Subtype.val (pow_orderOf_eq_one x)
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      rw [← Units.val_pow_eq_pow_val]
      change ((x : GL (Fin 2) ℂ) ^ orderOf x : GL (Fin 2) ℂ).val = 1
      rw [h1, Units.val_one]
    obtain ⟨α, hα'⟩ := trace_mem_range_of_pow_eq_one ιC _ hn hpow
    have hα : ιC α = (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ).trace := hα'
    refine ⟨α, by rw [hα, htr₀], fun v σ hv hσ => ?_⟩
    have htr := (hfr v σ hv hσ).1
    have hsum : (∑ i, (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i i, hmem σ i i⟩ : genRing ιC E)) =
        ⟨ιC α, iotaC_mem_genRing ιC E α⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ).trace = ιC α
      rw [htr, ← htr₀, hα]
    change (Matrix.trace fun i j => (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j) = ιL α
    simp only [Matrix.trace, Matrix.diag, hentry, ← map_sum, hsum, g', RingHom.comp_apply, hφ]
    rfl
  · refine ⟨Matrix.GeneralLinearGroup.det.comp ρh,
      (hρfin.image Matrix.GeneralLinearGroup.det).subset
        (by rintro _ ⟨σ, rfl⟩; exact ⟨ρh σ, ⟨σ, rfl⟩, rfl⟩), fun σ => ?_⟩
    simp only [sub_self, zpow_zero, mul_one]
    rfl

end ArtinMain



/-! ## §18. H-22 and H-10 closed

`R14Det` from Diamond–Shurman's two printed theorems (all three glue Props proved), and `EigenformHT`
from its newform case, the kernel's I4-L5 and the same two printed theorems. -/

section Closed

open ZInQ.Contrib.G9.PkgI4

/-- **H-22 closed.** `R14Det` from the two printed theorems `DSThm965` (Deligne, via Diamond–Shurman
Thm 9.6.5) and `DSThm966` (Deligne–Serre, via Diamond–Shurman Thm 9.6.6) only. -/
theorem r14Det_of_printed (hD : DSThm965) (hDS : DSThm966) : G0Galois.R14Det :=
  r14Det_of_wt (artinTransport_proof hDS)
    (r14DetWtGe2_of_ds hD semisimplification2_proof detFromFrobenius_proof)

/-- **H-10 from its newform case and the kernel's leaves** (`NewformOfEigenform` = I4-L5,
`EigenformRepExists` = R14 without the determinant). -/
theorem eigenformHT_of_kato (hNew : EigenformHTNew) (hL5 : NewformOfEigenform)
    (hR : EigenformRepExists) : EigenformHT :=
  eigenformHT_of_new hNew hL5 hR attachedConj_proof htConj_proof

/-- `EigenformRepExists` (R14 without the determinant) from `R14Det`. -/
theorem eigenformRepExists_of_r14Det (h : G0Galois.R14Det) : EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hatt, -⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨ρ, hss, hatt⟩

/-- **H-10 from its newform case, the kernel's I4-L5 and Diamond–Shurman's two printed theorems.** -/
theorem eigenformHT_of_kato_ds (hNew : EigenformHTNew) (hL5 : NewformOfEigenform)
    (hD : DSThm965) (hDS : DSThm966) : EigenformHT :=
  eigenformHT_of_kato hNew hL5 (eigenformRepExists_of_r14Det (r14Det_of_printed hD hDS))

end Closed



/-! ## §19. H-32 from `B_dR^{G_{ℚ_p}} = ℚ_p` alone

Fontaine's Tannakian theorem for `B_dR` (the leaf `FontaineDRTannakian` of §7) has an elementary proof
from the regularity of `B_dR` (Brinon–Conrad, Thm 5.2.1). `B_dR` is a field (bdr-kertheta, in the kernel:
`BdrKer.Cp.isField_BDeRham`), so regularity reduces to `B_dR^{G_{ℚ_p}} = ℚ_p`, the leaf
`BdRInvariants`. -/

section BdRSec

/-- **LEAF (Fontaine: `B_dR^{G_K} = K`, here `K = ℚ_p`).** Fontaine, *Le corps des périodes
p-adiques*, Astérisque 223 (1994), Exp. II, §1.5 (and §3); Brinon–Conrad, *CMI summer school notes on
p-adic Hodge theory* (2009), Thm 4.3.? / §4.4 (`(B_dR)^{G_K} = K`); numbering UNVERIFIED. Lean form: a
`G_{ℚ_p}`-invariant element of Mathlib's `B_dR(𝓞_ℂ_p)` (pkg-I4's action `bdrAct`) lies in the image
of `ℚ_p`. (It is the hypothesis `hfix` of pkg-I4's `isDeRham_trivial`.) -/
def BdRInvariants : Prop :=
  ∀ x : BdR p, (∀ σ : GQp p, bdrAct p σ x = x) → x ∈ Set.range (qpToBdR p)

theorem isField_BdR : IsField (BdR p) := BdrKer.Cp.isField_BDeRham p

/-- `B_dR` as a field (the ring structure is Mathlib's). -/
noncomputable def bdrField : Field (BdR p) := (isField_BdR p).toField

attribute [local instance] bdrField

variable {n : ℕ}

/-- The matrix of `ρ(σ)` read in `B_dR`. -/
def matB (M : Matrix (Fin n) (Fin n) ℚ_[p]) : Matrix (Fin n) (Fin n) (BdR p) :=
  M.map (algebraMap ℚ_[p] (BdR p))

/-- `σ` on `B_dRⁿ`, coordinatewise. -/
def bAct (σ : GQp p) (x : Fin n → BdR p) : Fin n → BdR p := fun k => bdrAct p σ (x k)

theorem mem_ddrStd_iff (ρ : GQp p →* GL (Fin n) ℚ_[p]) (x : Fin n → BdR p) :
    x ∈ ddrStd p ρ ↔ ∀ σ, (matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec (bAct p σ x) = x :=
  Iff.rfl

theorem matB_mul (A B : Matrix (Fin n) (Fin n) ℚ_[p]) : matB p (A * B) = matB p A * matB p B := by
  simp [matB, Matrix.map_mul]

theorem matB_one : matB p (1 : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  simp [matB, Matrix.map_one]

theorem matB_inv_mul (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) :
    matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) * matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  rw [← matB_mul, gl_inv_mul, matB_one]

theorem matB_mul_inv (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) :
    matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  rw [← matB_mul, gl_mul_inv, matB_one]

theorem bAct_of_mem {ρ : GQp p →* GL (Fin n) ℚ_[p]} {x : Fin n → BdR p} (hx : x ∈ ddrStd p ρ)
    (σ : GQp p) : bAct p σ x = (matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec x := by
  conv_rhs => rw [← (mem_ddrStd_iff p ρ x).mp hx σ]
  rw [Matrix.mulVec_mulVec, matB_inv_mul, Matrix.one_mulVec]

theorem bAct_add (σ : GQp p) (x y : Fin n → BdR p) : bAct p σ (x + y) = bAct p σ x + bAct p σ y := by
  ext k; simp [bAct]

theorem bAct_smul (σ : GQp p) (c : BdR p) (x : Fin n → BdR p) :
    bAct p σ (c • x) = bdrAct p σ c • bAct p σ x := by
  ext k; simp [bAct]

theorem bAct_sum {ι : Type*} (s : Finset ι) (σ : GQp p) (f : ι → Fin n → BdR p) :
    bAct p σ (∑ k ∈ s, f k) = ∑ k ∈ s, bAct p σ (f k) := by
  ext m; simp [bAct, Finset.sum_apply, map_sum]

theorem bAct_zero (σ : GQp p) : bAct p σ (0 : Fin n → BdR p) = 0 := by ext; simp [bAct]

theorem algebraMap_BdR_injective : Function.Injective (algebraMap ℚ_[p] (BdR p)) :=
  (algebraMap ℚ_[p] (BdR p)).injective

/-- **(I) Regularity.** `ℚ_p`-independent elements of `D_dR(V)` are `B_dR`-independent. -/
theorem ddrStd_linearIndependent (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p])
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → (Fin n → BdR p)) (hx : ∀ k, x k ∈ ddrStd p ρ)
    (hind : LinearIndependent ℚ_[p] x) : LinearIndependent (BdR p) x := by
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ (s : Finset ι) (b : ι → BdR p), (∀ k ∉ s, b k = 0) → ∑ k, b k • x k = 0 →
      ∀ k, b k = 0 from fun b hb => H Finset.univ b (by simp) hb
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hbs hb
  by_contra hne
  push_neg at hne
  obtain ⟨k₀, hk₀⟩ := hne
  have hk₀s : k₀ ∈ s := by
    by_contra h; exact hk₀ (hbs k₀ h)
  let b' : ι → BdR p := fun k => (b k₀)⁻¹ * b k
  have hb' : ∑ k, b' k • x k = 0 := by
    simp only [b', mul_smul, ← Finset.smul_sum, hb, smul_zero]
  have hb'k₀ : b' k₀ = 1 := inv_mul_cancel₀ hk₀
  have hb's : ∀ k ∉ s, b' k = 0 := fun k hk => by simp [b', hbs k hk]
  have key : ∀ σ, ∀ k, b' k = bdrAct p σ (b' k) := by
    intro σ
    let d : ι → BdR p := fun k => b' k - bdrAct p σ (b' k)
    have h1 : (matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec
        (∑ k, bdrAct p σ (b' k) • x k) = 0 := by
      have h0 := congrArg (bAct p σ) hb'
      rw [bAct_sum, bAct_zero] at h0
      rw [Matrix.mulVec_sum, ← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [bAct_smul, bAct_of_mem p (hx k), Matrix.mulVec_smul]
    have h2 : ∑ k, bdrAct p σ (b' k) • x k = 0 := by
      have := congrArg (matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])).mulVec h1
      rwa [Matrix.mulVec_mulVec, matB_mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have hd : ∑ k, d k • x k = 0 := by
      simp only [d, sub_smul, Finset.sum_sub_distrib, hb', h2, sub_zero]
    have hds : ∀ k ∉ s.erase k₀, d k = 0 := by
      intro k hk
      by_cases hkk : k = k₀
      · subst hkk; simp [d, hb'k₀]
      · have : k ∉ s := fun h => hk (Finset.mem_erase.mpr ⟨hkk, h⟩)
        simp [d, hb's k this]
    have := ih (s.erase k₀) (Finset.erase_ssubset hk₀s) d hds hd
    intro k
    exact sub_eq_zero.mp (this k)
  have hK : ∀ k, ∃ a : ℚ_[p], b' k = algebraMap ℚ_[p] (BdR p) a := by
    intro k
    obtain ⟨a, ha⟩ := hB (b' k) fun σ => (key σ k).symm
    exact ⟨a, ha.symm⟩
  choose a ha using hK
  have hsum : ∑ k, a k • x k = 0 := by
    rw [← hb']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha k, algebraMap_smul]
  have h0 := Fintype.linearIndependent_iff.mp hind a hsum k₀
  have h1 := ha k₀
  rw [h0, map_zero, hb'k₀] at h1
  exact one_ne_zero h1

theorem ddrStd_finiteDimensional (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p]) :
    FiniteDimensional ℚ_[p] (ddrStd p ρ) := by
  classical
  refine Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt (rank_le (n := n) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0 (n := n)))
  have hli : LinearIndependent (BdR p) (fun x : s => ((x : ddrStd p ρ) : Fin n → BdR p)) :=
    ddrStd_linearIndependent p hB ρ _ (fun x => (x : ddrStd p ρ).2)
      (LinearIndependent.map' hs (ddrStd p ρ).subtype (Submodule.ker_subtype _))
  calc s.card = Fintype.card s := (Fintype.card_coe s).symm
    _ ≤ Module.finrank (BdR p) (Fin n → BdR p) := hli.fintype_card_le_finrank
    _ = n := Module.finrank_fin_fun _

theorem ddrStd_finrank_le (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p]) :
    Module.finrank ℚ_[p] (ddrStd p ρ) ≤ n := by
  haveI := ddrStd_finiteDimensional p hB ρ
  let b := Module.finBasis ℚ_[p] (ddrStd p ρ)
  have hli : LinearIndependent (BdR p) (fun k => ((b k : ddrStd p ρ) : Fin n → BdR p)) :=
    ddrStd_linearIndependent p hB ρ _ (fun k => (b k).2)
      (LinearIndependent.map' b.linearIndependent (ddrStd p ρ).subtype (Submodule.ker_subtype _))
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin, Module.finrank_fin_fun] at this

end BdRSec

section BdRSec2

attribute [local instance] bdrField

instance bdrDomain : IsDomain (BdR p) := (isField_BdR p).isDomain

variable {n : ℕ}

theorem mulVec_eq_sum_col (P : Matrix (Fin n) (Fin n) (BdR p)) (v : Fin n → BdR p) :
    P.mulVec v = ∑ j, v j • (fun i => P i j) := by
  ext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem bAct_col (σ : GQp p) (P : Matrix (Fin n) (Fin n) (BdR p)) (j : Fin n) :
    bAct p σ (fun i => P i j) = fun i => P.map (bdrAct p σ) i j := rfl

/-- **(L5)** An invertible matrix whose columns lie in `D_dR(V)` makes `V` de Rham. -/
theorem isDeRhamStd_of_matrix (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p])
    (P : Matrix (Fin n) (Fin n) (BdR p)) (hP : P.det ≠ 0)
    (hrel : ∀ σ, matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * P.map (bdrAct p σ) = P) :
    IsDeRhamStd p ρ := by
  haveI := ddrStd_finiteDimensional p hB ρ
  have hcol : ∀ j, (fun i => P i j) ∈ ddrStd p ρ := by
    intro j
    rw [mem_ddrStd_iff]
    intro σ
    rw [bAct_col]
    ext i
    have := congrFun (congrFun (hrel σ) i) j
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mulVec, dotProduct]
    exact this
  let c : Fin n → ddrStd p ρ := fun j => ⟨fun i => P i j, hcol j⟩
  have hli : LinearIndependent ℚ_[p] c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : P.mulVec (fun j => algebraMap ℚ_[p] (BdR p) (a j)) = 0 := by
      rw [mulVec_eq_sum_col]
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum, Submodule.coe_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [algebraMap_smul]
      rfl
    by_contra hne
    exact hP ((Matrix.exists_mulVec_eq_zero_iff).mp
      ⟨_, fun h => hne (algebraMap_BdR_injective p (by simpa using congrFun h j)), h1⟩)
  have h1 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h1
  exact le_antisymm (ddrStd_finrank_le p hB ρ) h1

/-- **(L4)** If `V` is de Rham, a basis of `D_dR(V)` gives an invertible matrix. -/
theorem exists_matrix_of_isDeRhamStd (hB : BdRInvariants p) (ρ : GQp p →* GL (Fin n) ℚ_[p])
    (h : IsDeRhamStd p ρ) : ∃ P : Matrix (Fin n) (Fin n) (BdR p), P.det ≠ 0 ∧
      ∀ σ, matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * P.map (bdrAct p σ) = P := by
  haveI := ddrStd_finiteDimensional p hB ρ
  let b := (Module.finBasis ℚ_[p] (ddrStd p ρ)).reindex (finCongr h)
  let P : Matrix (Fin n) (Fin n) (BdR p) := Matrix.of fun i j => (b j : Fin n → BdR p) i
  have hli : LinearIndependent (BdR p) (fun j => ((b j : ddrStd p ρ) : Fin n → BdR p)) :=
    ddrStd_linearIndependent p hB ρ _ (fun j => (b j).2)
      (LinearIndependent.map' b.linearIndependent (ddrStd p ρ).subtype (Submodule.ker_subtype _))
  refine ⟨P, fun hdet => ?_, fun σ => ?_⟩
  · obtain ⟨v, hv, hPv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
    rw [mulVec_eq_sum_col] at hPv
    exact hv (funext fun j => Fintype.linearIndependent_iff.mp hli v hPv j)
  · ext i j
    have := congrFun ((mem_ddrStd_iff p ρ _).mp (b j).2 σ) i
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, bAct, P] using this

theorem map_inv_bdr (σ : GQp p) (P : Matrix (Fin n) (Fin n) (BdR p)) (hP : P.det ≠ 0) :
    (P⁻¹).map (bdrAct p σ) = (P.map (bdrAct p σ))⁻¹ := by
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **(a) Duals.** -/
theorem dual_of_bdr (hB : BdRInvariants p) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p])
    (h' : ∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) = ((ρ σ)⁻¹ : GL (Fin n) ℚ_[p]).val.transpose)
    (h : IsDeRhamStd p ρ) : IsDeRhamStd p ρ' := by
  obtain ⟨P, hP, hrel⟩ := exists_matrix_of_isDeRhamStd p hB ρ h
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine isDeRhamStd_of_matrix p hB ρ' (P⁻¹).transpose ?_ fun σ => ?_
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det P hu).ne_zero
  · have hPσ : P.map (bdrAct p σ) = matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) * P := by
      conv_rhs => rw [← hrel σ]
      rw [← mul_assoc, matB_inv_mul, one_mul]
    have hPσdet : (P.map (bdrAct p σ)).det ≠ 0 := by
      rw [hPσ, Matrix.det_mul]
      refine mul_ne_zero ?_ hP
      intro h0
      have := congrArg Matrix.det (matB_inv_mul p ρ σ)
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hinv : (P.map (bdrAct p σ))⁻¹ = P⁻¹ * matB p (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) := by
      apply Matrix.inv_eq_left_inv
      rw [hPσ, mul_assoc, ← mul_assoc (matB p _), matB_mul_inv, one_mul,
        Matrix.nonsing_inv_mul _ hu]
    have hmat' : matB p (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
        (matB p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p])).transpose := by
      rw [h' σ, ← map_inv, matB, matB, Matrix.transpose_map]
    rw [Matrix.transpose_map, map_inv_bdr p σ P hP, hinv, hmat', Matrix.transpose_mul,
      ← mul_assoc, ← Matrix.transpose_mul, matB_mul_inv, Matrix.transpose_one, one_mul]

end BdRSec2

section BdRSec3

attribute [local instance] bdrField

/-- **(d) Tensor products.** -/
theorem tensor_of_bdr (hB : BdRInvariants p) {a b : ℕ} (ρ : GQp p →* GL (Fin (a * b)) ℚ_[p])
    (ρ₁ : GQp p →* GL (Fin a) ℚ_[p]) (ρ₂ : GQp p →* GL (Fin b) ℚ_[p])
    (h : ∀ σ, (ρ σ : Matrix (Fin (a * b)) (Fin (a * b)) ℚ_[p]) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p])
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p])))
    (h₁ : IsDeRhamStd p ρ₁) (h₂ : IsDeRhamStd p ρ₂) : IsDeRhamStd p ρ := by
  obtain ⟨P₁, hP₁, hr₁⟩ := exists_matrix_of_isDeRhamStd p hB ρ₁ h₁
  obtain ⟨P₂, hP₂, hr₂⟩ := exists_matrix_of_isDeRhamStd p hB ρ₂ h₂
  refine isDeRhamStd_of_matrix p hB ρ
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) P₁ P₂)) ?_ ?_
  · rw [Matrix.det_reindex_self]
    rw [Matrix.det_kronecker]
    exact mul_ne_zero (pow_ne_zero _ hP₁) (pow_ne_zero _ hP₂)
  · intro σ
    have hm : matB p (ρ σ : Matrix (Fin (a * b)) (Fin (a * b)) ℚ_[p]) =
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (matB p (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]))
            (matB p (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) := by
      rw [h σ]; ext i j; simp [matB, Matrix.kroneckerMap_apply, map_mul]
    have hK : (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) P₁ P₂)).map (bdrAct p σ) =
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (P₁.map (bdrAct p σ)) (P₂.map (bdrAct p σ))) := by
      ext i j; simp [Matrix.kroneckerMap_apply, map_mul]
    rw [hm, hK, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      ← Matrix.reindex_apply]
    rw [← Matrix.mul_kronecker_mul, hr₁ σ, hr₂ σ]

/-- **(c) Direct sums.** -/
theorem sum_of_bdr (hB : BdRInvariants p) {a b : ℕ} (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p])
    (ρ₁ : GQp p →* GL (Fin a) ℚ_[p]) (ρ₂ : GQp p →* GL (Fin b) ℚ_[p])
    (h : ∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) 0 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p])))
    (h₁ : IsDeRhamStd p ρ₁) (h₂ : IsDeRhamStd p ρ₂) : IsDeRhamStd p ρ := by
  obtain ⟨P₁, hP₁, hr₁⟩ := exists_matrix_of_isDeRhamStd p hB ρ₁ h₁
  obtain ⟨P₂, hP₂, hr₂⟩ := exists_matrix_of_isDeRhamStd p hB ρ₂ h₂
  refine isDeRhamStd_of_matrix p hB ρ
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P₁ 0 0 P₂)) ?_ ?_
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero hP₁ hP₂
  · intro σ
    have hm : matB p (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (matB p (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p])) 0 0
            (matB p (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) := by
      rw [h σ, matB, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map,
        Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
      rfl
    have hK : (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P₁ 0 0 P₂)).map
        (bdrAct p σ) = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (P₁.map (bdrAct p σ)) 0 0 (P₂.map (bdrAct p σ))) := by
      rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map,
        Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    rw [hm, hK, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, hr₁ σ, hr₂ σ]
    simp

end BdRSec3

section BdRSec4

attribute [local instance] bdrField

theorem blk_mulVec_inl {a b : ℕ} (A : Matrix (Fin a) (Fin a) (BdR p)) (C : Matrix (Fin b) (Fin a) (BdR p))
    (D : Matrix (Fin b) (Fin b) (BdR p)) (x : Fin (a + b) → BdR p) (i : Fin a) :
    ((Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 C D)).mulVec x)
      (finSumFinEquiv (Sum.inl i)) = A.mulVec (fun i => x (finSumFinEquiv (Sum.inl i))) i := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def]

theorem blk_mulVec_inr {a b : ℕ} (A : Matrix (Fin a) (Fin a) (BdR p)) (C : Matrix (Fin b) (Fin a) (BdR p))
    (D : Matrix (Fin b) (Fin b) (BdR p)) (x : Fin (a + b) → BdR p) (j : Fin b) :
    ((Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 C D)).mulVec x)
      (finSumFinEquiv (Sum.inr j)) =
      (C.mulVec (fun i => x (finSumFinEquiv (Sum.inl i))) +
        D.mulVec (fun j => x (finSumFinEquiv (Sum.inr j)))) j := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def]

/-- **(b) Sub and quotient** (block lower triangular). -/
theorem sub_of_bdr (hB : BdRInvariants p) {a b : ℕ} (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p])
    (ρ₁ : GQp p →* GL (Fin a) ℚ_[p]) (ρ₂ : GQp p →* GL (Fin b) ℚ_[p])
    (Y : GQp p → Matrix (Fin b) (Fin a) ℚ_[p])
    (h : ∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) 0 (Y σ)
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p])))
    (hρ : IsDeRhamStd p ρ) : IsDeRhamStd p ρ₁ ∧ IsDeRhamStd p ρ₂ := by
  haveI := ddrStd_finiteDimensional p hB ρ
  haveI := ddrStd_finiteDimensional p hB ρ₁
  haveI := ddrStd_finiteDimensional p hB ρ₂
  set e := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
  have hm : ∀ σ, matB p (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex e e (Matrix.fromBlocks (matB p (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p])) 0
        ((Y σ).map (algebraMap ℚ_[p] (BdR p))) (matB p (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) := by
    intro σ
    rw [h σ, matB, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map,
      Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    rfl
  let π₁ : ddrStd p ρ →ₗ[ℚ_[p]] ddrStd p ρ₁ :=
    { toFun := fun x => ⟨fun i => (x : Fin (a + b) → BdR p) (e (Sum.inl i)), by
        rw [mem_ddrStd_iff]
        intro σ
        ext i
        have := congrFun ((mem_ddrStd_iff p ρ _).mp x.2 σ) (e (Sum.inl i))
        rw [hm, blk_mulVec_inl] at this
        exact this⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hker : ∀ x ∈ LinearMap.ker π₁, ∀ i, (x : Fin (a + b) → BdR p) (e (Sum.inl i)) = 0 := by
    intro x hx i
    have := congrArg (fun z : ddrStd p ρ₁ => (z : Fin a → BdR p) i) (LinearMap.mem_ker.mp hx)
    exact this
  let κ : LinearMap.ker π₁ →ₗ[ℚ_[p]] ddrStd p ρ₂ :=
    { toFun := fun x => ⟨fun j => ((x : ddrStd p ρ) : Fin (a + b) → BdR p) (e (Sum.inr j)), by
        rw [mem_ddrStd_iff]
        intro σ
        ext j
        have := congrFun ((mem_ddrStd_iff p ρ _).mp (x : ddrStd p ρ).2 σ) (e (Sum.inr j))
        rw [hm, blk_mulVec_inr] at this
        have h0 : (fun i => bAct p σ ((x : ddrStd p ρ) : Fin (a + b) → BdR p) (e (Sum.inl i))) = 0 := by
          funext i
          simp only [bAct, hker x x.2 i, map_zero, Pi.zero_apply]
        rw [h0, Matrix.mulVec_zero, zero_add] at this
        exact this⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hκ : Function.Injective κ := by
    intro x y hxy
    apply Subtype.ext; apply Subtype.ext
    funext k
    obtain ⟨k', rfl⟩ := e.surjective k
    rcases k' with i | j
    · rw [hker x x.2 i, hker y y.2 i]
    · exact congrFun (congrArg Subtype.val hxy) j
  have h1 := LinearMap.finrank_range_add_finrank_ker π₁
  have h2 : Module.finrank ℚ_[p] (LinearMap.range π₁) ≤ Module.finrank ℚ_[p] (ddrStd p ρ₁) :=
    Submodule.finrank_le _
  have h3 := LinearMap.finrank_le_finrank_of_injective hκ
  have h4 := ddrStd_finrank_le p hB ρ₁
  have h5 := ddrStd_finrank_le p hB ρ₂
  unfold IsDeRhamStd at hρ ⊢
  constructor <;> omega

/-- **Fontaine's Tannakian theorem for `B_dR` from `B_dR^{G_{ℚ_p}} = ℚ_p`.** -/
theorem fontaineDRTannakian_of_bdrInvariants (hB : BdRInvariants p) : FontaineDRTannakian p :=
  ⟨fun _ ρ ρ' _ h' h => dual_of_bdr p hB ρ ρ' h' h,
    fun _ _ ρ ρ₁ ρ₂ Y _ h hρ => sub_of_bdr p hB ρ ρ₁ ρ₂ Y h hρ,
    fun _ _ ρ ρ₁ ρ₂ _ _ h h₁ h₂ => sum_of_bdr p hB ρ ρ₁ ρ₂ h h₁ h₂,
    fun _ _ ρ ρ₁ ρ₂ _ _ h h₁ h₂ => tensor_of_bdr p hB ρ ρ₁ ρ₂ h h₁ h₂⟩

/-- **H-32 from `B_dR^{G_{ℚ_p}} = ℚ_p` alone.** -/
theorem t23_all_of_bdrInvariants (hB : ∀ (p : ℕ) [Fact p.Prime], BdRInvariants p) :
    ∀ (p : ℕ) [Fact p.Prime], T23_FontaineClosure p :=
  fun p _ => t23_of_fontaine p (fontaineDRTannakian_of_bdrInvariants p (hB p))

end BdRSec4

/-! ## Summary: six of the seven rows from the published-form leaves (and Kato's newform case) -/

/-- **The p-adic Hodge theory rows of the frontier.** H-52, H-32, H-8, H-22, H-51 from seven
published-form leaves (Tate's two theorems, the Hodge–Tate decomposition of `V_p(A)`, the de Rham
property of `H¹`, `B_dR^{G_{ℚ_p}} = ℚ_p`, Diamond–Shurman 9.6.5 and 9.6.6); H-10 also from
`EigenformHTNew` (Kato's theorem for newforms, not statable in Mathlib today) and the kernel's leaf I4-L5
`NewformOfEigenform`. (H-9 needs `B_st`.) -/
theorem hodge_rows_of_leaves (hT : TateTwistInvariants) (hA : AxSenTate)
    (hHT : HodgeTateDecompAbVar) (hdR : DeRhamH1AbVarT)
    (hB : ∀ (p : ℕ) [Fact p.Prime], BdRInvariants p) (hD : DSThm965) (hDS : DSThm966)
    (hNew : EigenformHTNew) (hL5 : NewformOfEigenform) :
    G0Galois.FiniteImageHT ∧ (∀ (p : ℕ) [Fact p.Prime], T23_FontaineClosure p) ∧
      ZInQ.Contrib.R10.DeRhamComparisonHT ∧ G0Galois.R14Det ∧ G0Galois.SenTwist ∧ EigenformHT :=
  ⟨finiteImageHT_of_tate hT hA, t23_all_of_bdrInvariants hB,
    deRhamComparisonHT_of_leavesT hHT hT hA hdR, r14Det_of_printed hD hDS, senTwist_of_tate hT hA,
    eigenformHT_of_kato_ds hNew hL5 hD hDS⟩

end

end ZInQ.Contrib.HodgeSplit
