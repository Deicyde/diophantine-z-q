
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
    (hind : ∀ j₀, LinearIndependent K (fun k : {k // j k = j₀} => y k)) :
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
  choose a ha using fun k : {k // j k = j k₀} => hKval k.1 k.2
  have hsum : ∑ k : {k // j k = j k₀}, a k • y k = 0 := by
    have e1 : ∀ k : {k // j k = j k₀}, a k • y k = b' k • y k := by
      intro k; rw [ha k, algebraMap_smul]
    simp only [e1]
    rw [← hb', ← Finset.sum_subtype (Finset.univ.filter fun k => j k = j k₀) (by simp)
      (fun k => b' k • y k), Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · rw [hzero k h, zero_smul]
  have := Fintype.linearIndependent_iff.mp (hind (j k₀)) a hsum ⟨k₀, rfl⟩
  have h1 := ha ⟨k₀, rfl⟩
  rw [this, map_zero, hb'k₀] at h1
  exact one_ne_zero h1

end SenSec
