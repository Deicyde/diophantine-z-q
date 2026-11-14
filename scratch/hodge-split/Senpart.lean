
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
  rw [PkgI4.cycPow_mul, PkgI4.cycPow_mul, mul_comm (cycPow p g i), mul_assoc,
    ← PkgI4.cycPow_mul, mul_inv_cancel, PkgI4.cycPow_one, mul_one]

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
