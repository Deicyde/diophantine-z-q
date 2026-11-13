import ZInQKernel.Contrib.UnramRoots.Reduction
import ZInQKernel.Contrib.UnramRoots.Metric
import ZInQKernel.Contrib.UnramRoots.FrobData

-- Adopted by task frob-contrib from scratch/unram-roots/part_procyclic.lean (task unram-roots); imports and `noncomputable section` added (the scratch file was concatenated after Reduction.lean, whose section stays open).

/-! ## `UnramProcyclic` from the Frobenius data (proved)

TC-free: Frobenius data (`FrobData`, from Tau Ceti in `frobData_exists`), the metric lemmas, and
Mathlib's finite and infinite Galois correspondence. -/

noncomputable section

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond Polynomial IntermediateField

variable {p : ℕ} [Fact p.Prime]

theorem pow_modEq_pow_mod (q n k : ℕ) (hq : 0 < q) : q ^ k ≡ q ^ (k % n) [MOD q ^ n - 1] := by
  have h1 : q ^ n ≡ 1 [MOD q ^ n - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hq)
  calc q ^ k = (q ^ n) ^ (k / n) * q ^ (k % n) := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (k / n) * q ^ (k % n) [MOD q ^ n - 1] := (h1.pow _).mul_right _
    _ = q ^ (k % n) := by rw [one_pow, one_mul]

theorem modEq_of_pow_modEq {q n k k' : ℕ} (hq : 1 < q) (hn : 0 < n)
    (h : q ^ k ≡ q ^ k' [MOD q ^ n - 1]) : k ≡ k' [MOD n] := by
  have h' : q ^ (k % n) ≡ q ^ (k' % n) [MOD q ^ n - 1] :=
    ((pow_modEq_pow_mod q n k (by omega)).symm.trans h).trans (pow_modEq_pow_mod q n k' (by omega))
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · have : n = 1 := by omega
    subst this
    exact Nat.modEq_one
  have hbound : ∀ r, r < n → q ^ r < q ^ n - 1 := by
    intro r hr
    have h1 : q ^ r ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : q ^ n = q * q ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have h3 : q ≤ q ^ (n - 1) := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 2 * q ^ (n - 1) ≤ q ^ n := by rw [h2]; exact Nat.mul_le_mul_right _ hq
    omega
  have := Nat.ModEq.eq_of_lt_of_lt h' (hbound _ (Nat.mod_lt _ hn)) (hbound _ (Nat.mod_lt _ hn))
  exact Nat.pow_right_injective hq this

/-- The exponent by which `σ` acts on the roots of `X^{q^n} − X` is unique modulo `n`. -/
theorem modEq_of_act {q n k k' : ℕ} (hq : 1 < q) (hn : 0 < n)
    (h : ∀ x : Kbar p, x ^ q ^ n = x → x ^ q ^ k = x ^ q ^ k') : k ≡ k' [MOD n] := by
  set N := q ^ n - 1 with hNdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  have hN : 0 < N := by omega
  haveI : NeZero (N : Kbar p) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (Kbar p) N
  have hζN : ζ ^ q ^ n = ζ := by
    rw [show q ^ n = N + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  have e := h ζ hζN
  rw [← pow_mod_of_pow_eq_one hζ.pow_eq_one (q ^ k),
    ← pow_mod_of_pow_eq_one hζ.pow_eq_one (q ^ k')] at e
  exact modEq_of_pow_modEq hq hn (hζ.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) e)

theorem pow_pow_of_dvd {q f N : ℕ} {x : Kbar p} (hx : x ^ q ^ f = x) (h : f ∣ N) :
    x ^ q ^ N = x := by
  obtain ⟨j, rfl⟩ := h
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]

theorem mem_rootSet_Qp {q f : ℕ} (hq : 1 < q) (hf : 0 < f) {x : Kbar p}
    (hx : x ^ q ^ f = x) : x ∈ (X ^ q ^ f - X : ℚ_[p][X]).rootSet (Kbar p) := by
  have hdeg : 1 < q ^ f := Nat.one_lt_pow hf.ne' hq
  have hne : (X ^ q ^ f - X : ℚ_[p][X]) ≠ 0 :=
    (monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hdeg)).ne_zero
  rw [mem_rootSet_of_ne hne]
  simp [hx]

theorem fix_adjoin {σ : GQp p} {S : Set (Kbar p)} (h : ∀ x ∈ S, σ x = x) :
    ∀ x ∈ adjoin ℚ_[p] S, σ x = x := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact σ.commutes r
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/-- (F2) from the Frobenius data. -/
theorem f2_of_frobData {F : Fld p} [FiniteDimensional ℚ_[p] F] {q : ℕ} {φ : GQp p}
    (hD : FrobData F q φ) (n : ℕ) (hn : 0 < n) : ∃ χ : GQp p → ZMod n,
        (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, χ (σ * τ) = χ σ + χ τ) ∧ χ φ = 1 ∧
        (∀ σ ∈ fixSet F ∩ inertiaSet, χ σ = 0) ∧
        ∃ K : Fld p, FiniteDimensional ℚ_[p] K ∧ ∀ σ ∈ fixSet K, χ σ = 0 := by
  obtain ⟨hq1, ⟨e, hqe⟩, hφF, hφ, hS3⟩ := hD
  have hpq : p ∣ q := by
    rcases e with _ | e
    · rw [pow_zero] at hqe; omega
    · rw [hqe]; exact dvd_pow_self p (Nat.succ_ne_zero e)
  classical
  let kk : GQp p → ℕ := fun σ => if h : σ ∈ fixSet F then Classical.choose (hS3 σ h n hn) else 0
  have hkk : ∀ σ (h : σ ∈ fixSet F), ∀ x : Kbar p, x ^ q ^ n = x → σ x = x ^ q ^ kk σ := by
    intro σ h
    simp only [kk, dif_pos h]
    exact Classical.choose_spec (hS3 σ h n hn)
  have hzero : ∀ σ (h : σ ∈ fixSet F), (∀ x : Kbar p, x ^ q ^ n = x → σ x = x) →
      ((kk σ : ℕ) : ZMod n) = 0 := by
    intro σ h hfix
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff]
    apply modEq_of_act (p := p) hq1 hn
    intro x hx
    rw [← hkk σ h x hx, pow_zero, pow_one]
    exact hfix x hx
  refine ⟨fun σ => (kk σ : ZMod n), ?_, ?_, ?_, ?_⟩
  · intro σ hσ τ hτ
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
    apply modEq_of_act (p := p) hq1 hn
    intro x hx
    rw [← hkk _ (mul_mem_fixSet hσ hτ) x hx, AlgEquiv.mul_apply, hkk τ hτ x hx, map_pow,
      hkk σ hσ x hx, ← pow_mul, ← pow_add]
  · show ((kk φ : ℕ) : ZMod n) = 1
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    apply modEq_of_act (p := p) hq1 hn
    intro x hx
    rw [← hkk φ hφF x hx, hφ n x hn hx, pow_one]
  · intro σ hσ
    exact hzero σ hσ.1 fun x hx => fix_of_mem_inertiaSet_of_pow_eq_self hσ.2
      (Nat.one_lt_pow hn.ne' hq1) (dvd_pow hpq hn.ne') hx
  · set A : Fld p := adjoin ℚ_[p] ((X ^ q ^ n - X : ℚ_[p][X]).rootSet (Kbar p))
    haveI : FiniteDimensional ℚ_[p] A :=
      finiteDimensional_adjoin fun _ hx => (isAlgebraic_of_mem_rootSet hx).isIntegral
    refine ⟨F ⊔ A, inferInstance, fun σ hσ => ?_⟩
    refine hzero σ (fixSet_anti le_sup_left hσ) fun x hx => ?_
    exact hσ x ((le_sup_right : A ≤ F ⊔ A) (subset_adjoin _ _ (mem_rootSet_Qp hq1 hn hx)))

/-- The roots of `X^{q^f} − X`, `f ≥ 1`. -/
def Rq (q : ℕ) : Set (Kbar p) := {x | ∃ f : ℕ, 0 < f ∧ x ^ q ^ f = x}

/-- `F(R_N)`, as a field over `ℚ_p`. -/
def EN (F : Fld p) (q N : ℕ) : Fld p := adjoin ℚ_[p] ((F : Set (Kbar p)) ∪ {x | x ^ q ^ N = x})

/-- Every element of `F^{ur} = F(R)` lies in some `F(R_N)`. -/
theorem exists_mem_EN {F : Fld p} {q : ℕ} {y : Kbar p}
    (hy : y ∈ adjoin ℚ_[p] ((F : Set (Kbar p)) ∪ Rq q)) : ∃ N : ℕ, 0 < N ∧ y ∈ EN F q N := by
  classical
  obtain ⟨T, hTS, hyT⟩ := exists_finset_of_mem_adjoin hy
  let ff : Kbar p → ℕ := fun t => if h : t ∈ Rq q then Classical.choose h else 1
  have hff : ∀ t, 0 < ff t := by
    intro t
    by_cases h : t ∈ Rq q
    · simp only [ff, dif_pos h]; exact (Classical.choose_spec h).1
    · simp only [ff, dif_neg h]; exact Nat.one_pos
  set N := ∏ t ∈ T, ff t
  have hN : 0 < N := Finset.prod_pos fun t _ => hff t
  refine ⟨N, hN, adjoin.mono _ _ _ ?_ hyT⟩
  intro t ht
  rcases hTS ht with htF | htR
  · exact Or.inl htF
  · right
    have hspec := (Classical.choose_spec htR).2
    have hdvd : ff t ∣ N := Finset.dvd_prod_of_mem ff ht
    simp only [ff, dif_pos htR] at hdvd
    exact pow_pow_of_dvd hspec hdvd

/-- (F1) from the Frobenius data. -/
theorem f1_of_frobData {F : Fld p} [FiniteDimensional ℚ_[p] F] {q : ℕ} {φ : GQp p}
    (hD : FrobData F q φ) (K : Fld p) (hK : FiniteDimensional ℚ_[p] K) (hFK : F ≤ K)
    (σ : GQp p) (hσ : σ ∈ fixSet F) :
    ∃ k : ℕ, ∃ τ ∈ fixSet F ∩ inertiaSet, ∃ g ∈ fixSet K, σ = φ ^ k * τ * g := by
  obtain ⟨hq1, ⟨e, hqe⟩, hφF, hφ, hS3⟩ := hD
  haveI : IsGalois ℚ_[p] (Kbar p) := IsAlgClosure.isGalois ℚ_[p] (Kbar p)
  set E : Fld p := adjoin ℚ_[p] ((F : Set (Kbar p)) ∪ Rq q) with hE
  set M : Fld p := normalClosure ℚ_[p] K (Kbar p) with hM
  have hKM : K ≤ M := IntermediateField.le_normalClosure K
  set H₀ : Subgroup (M ≃ₐ[ℚ_[p]] M) := E.fixingSubgroup.map (AlgEquiv.restrictNormalHom M)
  -- the fixed field of `H₀` is `M ∩ E`
  have hfix : ∀ y : M, y ∈ fixedField H₀ → (y : Kbar p) ∈ E := by
    intro y hy
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have h1 := (mem_fixedField_iff H₀ y).1 hy (AlgEquiv.restrictNormalHom M τ) ⟨τ, hτ, rfl⟩
    have h2 : (((τ.restrictNormal M) y : M) : Kbar p) = τ y := AlgEquiv.restrictNormal_commutes τ M y
    change τ (y : Kbar p) = y
    rw [← h2]
    exact congrArg Subtype.val h1
  -- a uniform level `N`
  obtain ⟨N, hN, hNfix⟩ : ∃ N : ℕ, 0 < N ∧ ∀ y : M, y ∈ fixedField H₀ → (y : Kbar p) ∈ EN F q N := by
    classical
    let b := Module.finBasis ℚ_[p] (fixedField H₀)
    have hb : ∀ i, ∃ N : ℕ, 0 < N ∧ (((b i : fixedField H₀) : M) : Kbar p) ∈ EN F q N :=
      fun i => exists_mem_EN (hfix _ (b i).2)
    choose Nf hNf0 hNf using hb
    refine ⟨∏ i, Nf i, Finset.prod_pos fun i _ => hNf0 i, fun y hy => ?_⟩
    have hmono : ∀ i, EN F q (Nf i) ≤ EN F q (∏ i, Nf i) := by
      intro i
      apply adjoin.mono
      rintro x (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (pow_pow_of_dvd hx (Finset.dvd_prod_of_mem Nf (Finset.mem_univ i)))
    have hrepr := b.sum_repr ⟨y, hy⟩
    let L : (fixedField H₀) →ₗ[ℚ_[p]] Kbar p := (M.val.comp (fixedField H₀).val).toLinearMap
    have hL := congrArg L hrepr
    rw [map_sum] at hL
    simp only [LinearMap.map_smul] at hL
    have : (y : Kbar p) = ∑ i, (b.repr ⟨y, hy⟩ i) • (((b i : fixedField H₀) : M) : Kbar p) :=
      hL.symm
    rw [this]
    exact sum_mem fun i _ => smul_mem _ (hmono i (hNf i))
  -- Frobenius exponent at level `N`
  obtain ⟨k, hk⟩ := hS3 σ hσ N hN
  have hφk : ∀ j : ℕ, ∀ x : Kbar p, x ^ q ^ N = x → (φ ^ j) x = x ^ q ^ j := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      have hxq : (x ^ q) ^ q ^ N = x ^ q := by rw [← pow_mul, mul_comm, pow_mul, hx]
      rw [pow_succ', AlgEquiv.mul_apply, ih x hx, map_pow, hφ N x hN hx, ← pow_mul, ← pow_succ']
  set σ' : GQp p := (φ ^ k)⁻¹ * σ with hσ'
  have hσ'F : σ' ∈ fixSet F := mul_mem_fixSet (inv_mem_fixSet (pow_mem_fixSet hφF k)) hσ
  have hσ'N : ∀ x ∈ EN F q N, σ' x = x := by
    apply fix_adjoin
    rintro x (hx | hx)
    · exact hσ'F x hx
    · change (φ ^ k)⁻¹ (σ x) = x
      rw [hk x hx, ← hφk k x hx, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  -- Galois correspondence in `M / ℚ_p`
  have hσM : AlgEquiv.restrictNormalHom M σ' ∈ H₀ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H₀, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply Subtype.ext
    have h2 : (((σ'.restrictNormal M) y : M) : Kbar p) = σ' y :=
      AlgEquiv.restrictNormal_commutes σ' M y
    change ((σ'.restrictNormal M) y : Kbar p) = y
    rw [h2]
    exact hσ'N _ (hNfix y hy)
  obtain ⟨τ, hτE, hτσ⟩ := Subgroup.mem_map.1 hσM
  have hτE' : ∀ x ∈ E, τ x = x := fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτE x hx
  have hτM : ∀ y ∈ M, τ y = σ' y := by
    intro y hy
    have h1 : (((τ.restrictNormal M) ⟨y, hy⟩ : M) : Kbar p) = τ y :=
      AlgEquiv.restrictNormal_commutes τ M ⟨y, hy⟩
    have h2 : (((σ'.restrictNormal M) ⟨y, hy⟩ : M) : Kbar p) = σ' y :=
      AlgEquiv.restrictNormal_commutes σ' M ⟨y, hy⟩
    have h3 := congrArg (fun χ : M ≃ₐ[ℚ_[p]] M => ((χ ⟨y, hy⟩ : M) : Kbar p)) hτσ
    rw [← h1, ← h2]
    exact h3
  have hFE : (F : Set (Kbar p)) ⊆ E := fun x hx => subset_adjoin _ _ (Or.inl hx)
  refine ⟨k, τ, ⟨fun x hx => hτE' x (hFE hx), ?_⟩, τ⁻¹ * σ', ?_, ?_⟩
  · apply mem_inertiaSet_of_fix
    intro m hm t ht
    apply hτE'
    apply subset_adjoin
    right
    refine ⟨m, hm, ?_⟩
    rw [hqe, ← pow_mul, mul_comm, pow_mul]
    clear hqe
    induction e with
    | zero => simp
    | succ e ih => rw [pow_succ, pow_mul, ih, ht]
  · intro x hx
    have hxM := hKM hx
    change τ⁻¹ (σ' x) = x
    rw [← hτM x hxM, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  · rw [hσ']; group

/-- **`UnramProcyclic` from the Frobenius data (proved).** -/
theorem unramProcyclic_of_frobData
    (h : ∀ F : Fld p, FiniteDimensional ℚ_[p] F → ∃ q φ, FrobData F q φ) :
    UnramProcyclic p := by
  intro F hF
  obtain ⟨q, φ, hD⟩ := h F hF
  exact ⟨φ, hD.2.2.1, fun K hK hFK σ hσ => f1_of_frobData hD K hK hFK σ hσ,
    fun n hn => f2_of_frobData hD n hn⟩

end UnramRootsTask
