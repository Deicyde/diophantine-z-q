import Mathlib

/-! # Tate–Sen independence of twisted invariants

Let `L` be a field with an action of a set `G` by ring endomorphisms fixing a subfield `K`, let
`M` be an `L`-vector space with a semilinear additive action `S` of `G`, and let `w i σ ∈ K` be a
multiplicative family of scalars ("`χ(σ)^i`"). Suppose:

* (twists) `x ∈ L` with `w i σ • σ(x) = x` for every `σ` is `0` when `i ≠ 0`;
* (invariants) `x ∈ L` with `σ(x) = x` for every `σ` lies in `K`.

Then vectors `y_k ∈ M` with `w (j k) σ • S σ (y k) = y k` that are `K`-linearly independent within
each weight are `L`-linearly independent (`linearIndependent_of_twisted`). Consequently the
`K`-spaces of twisted invariants are finite-dimensional and their dimensions add up to at most
`dim_L M` (`sum_finrank_le`). This is the argument of Tate (1967, §3.3) for
`(ℂ_p(i) ⊗ V)^{G}`; here it is written for an abstract semilinear action.
-/

set_option autoImplicit false

namespace DeRhamHTMult

open Module

noncomputable section

section Indep

variable {K L M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module L M]
  [Module K M] [IsScalarTower K L M]
  (act : G → L →+* L) (S : G → M →+ M) (w : ℤ → G → K)

omit [Module L M] [IsScalarTower K L M] in
theorem smul_twist_eq {a : ℤ} {σ : G} (hw0 : ∀ σ, w 0 σ = 1)
    (hwadd : ∀ a b σ, w (a + b) σ = w a σ * w b σ) {y : M} (hy : w a σ • S σ y = y) :
    S σ y = w (-a) σ • y := by
  rw [← hy, smul_smul, ← hwadd, neg_add_cancel, hw0, one_smul, hy]

omit act S w in
theorem smul_comm_KL (c : K) (a : L) (y : M) : c • (a • y) = a • (c • y) := by
  rw [← algebraMap_smul L c (a • y), ← algebraMap_smul L c y, smul_smul, smul_smul, mul_comm]

/-- **Tate–Sen independence.** -/
theorem linearIndependent_of_twisted
    (hS : ∀ σ (c : L) y, S σ (c • y) = act σ c • S σ y)
    (hw0 : ∀ σ, w 0 σ = 1) (hwadd : ∀ a b σ, w (a + b) σ = w a σ * w b σ)
    (hT : ∀ i : ℤ, i ≠ 0 → ∀ x : L, (∀ σ, w i σ • act σ x = x) → x = 0)
    (hA : ∀ x : L, (∀ σ, act σ x = x) → ∃ a : K, x = algebraMap K L a)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι → ℤ) (y : ι → M)
    (hy : ∀ k σ, w (j k) σ • S σ (y k) = y k)
    (hind : ∀ (j₀ : ℤ) (a : ι → K), (∀ k, j k ≠ j₀ → a k = 0) → ∑ k, a k • y k = 0 →
      ∀ k, a k = 0) :
    LinearIndependent L y := by
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ (s : Finset ι) (b : ι → L), (∀ k ∉ s, b k = 0) → ∑ k, b k • y k = 0 →
      ∀ k, b k = 0 from fun b hb => H Finset.univ b (by simp) hb
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hbs hb
  by_contra hne
  push Not at hne
  obtain ⟨k₀, hk₀⟩ := hne
  have hk₀s : k₀ ∈ s := by
    by_contra h; exact hk₀ (hbs k₀ h)
  let b' : ι → L := fun k => (b k₀)⁻¹ * b k
  have hb' : ∑ k, b' k • y k = 0 := by
    simp only [b', mul_smul, ← Finset.smul_sum, hb, smul_zero]
  have hb'k₀ : b' k₀ = 1 := inv_mul_cancel₀ hk₀
  have hb's : ∀ k ∉ s, b' k = 0 := fun k hk => by simp [b', hbs k hk]
  have key : ∀ σ k, b' k = w (j k₀ - j k) σ • act σ (b' k) := by
    intro σ
    let d : ι → L := fun k => b' k - w (j k₀ - j k) σ • act σ (b' k)
    have h1 : ∑ k, (w (-j k) σ • act σ (b' k)) • y k = 0 := by
      have h0 := congrArg (S σ) hb'
      rw [map_sum, map_zero] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hS, smul_twist_eq S w hw0 hwadd (hy k σ), smul_assoc, smul_comm_KL]
    have hd : ∑ k, d k • y k = 0 := by
      have h3 : ∑ k, (w (j k₀ - j k) σ • act σ (b' k)) • y k = 0 := by
        have e : ∀ k, (w (j k₀ - j k) σ • act σ (b' k)) • y k =
            w (j k₀) σ • ((w (-j k) σ • act σ (b' k)) • y k) := by
          intro k
          rw [smul_assoc, smul_assoc, smul_smul, ← hwadd, sub_eq_add_neg]
        simp only [e]
        rw [← Finset.smul_sum, h1, smul_zero]
      simp only [d, sub_smul, Finset.sum_sub_distrib, hb', h3, sub_zero]
    have hds : ∀ k ∉ s.erase k₀, d k = 0 := by
      intro k hk
      by_cases hkk : k = k₀
      · subst hkk
        simp [d, hb'k₀, hw0]
      · have : k ∉ s := fun h => hk (Finset.mem_erase.mpr ⟨hkk, h⟩)
        simp [d, hb's k this]
    have := ih (s.erase k₀) (Finset.erase_ssubset hk₀s) d hds hd
    intro k
    exact sub_eq_zero.mp (this k)
  have hzero : ∀ k, j k ≠ j k₀ → b' k = 0 := by
    intro k hk
    exact hT (j k₀ - j k) (by omega) (b' k) fun σ => (key σ k).symm
  have hKval : ∀ k, j k = j k₀ → ∃ a : K, b' k = algebraMap K L a := by
    intro k hk
    refine hA (b' k) fun σ => ?_
    have := key σ k
    rw [hk, sub_self, hw0, one_smul] at this
    exact this.symm
  let a : ι → K := fun k => if h : j k = j k₀ then (hKval k h).choose else 0
  have ha : ∀ k, j k = j k₀ → b' k = algebraMap K L (a k) := by
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

variable [FiniteDimensional L M] (H : ℤ → Submodule K M)

/-- Twisted invariants are finite-dimensional: `dim_K H_i ≤ dim_L M`. -/
theorem finiteDimensional_twisted
    (hS : ∀ σ (c : L) y, S σ (c • y) = act σ c • S σ y)
    (hw0 : ∀ σ, w 0 σ = 1) (hwadd : ∀ a b σ, w (a + b) σ = w a σ * w b σ)
    (hT : ∀ i : ℤ, i ≠ 0 → ∀ x : L, (∀ σ, w i σ • act σ x = x) → x = 0)
    (hA : ∀ x : L, (∀ σ, act σ x = x) → ∃ a : K, x = algebraMap K L a)
    (hH : ∀ i, ∀ y ∈ H i, ∀ σ, w i σ • S σ y = y) (i : ℤ) :
    FiniteDimensional K (H i) := by
  classical
  haveI : Module.Free K (H i) := Module.Free.of_divisionRing K _
  refine Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt
    (rank_le (n := finrank L M) fun s hs => ?_) (Cardinal.natCast_lt_aleph0))
  have hli : LinearIndependent L (fun x : s => ((x : H i) : M)) := by
    refine linearIndependent_of_twisted act S w hS hw0 hwadd hT hA (fun _ => i) _
      (fun x σ => hH i _ (x : H i).2 σ) ?_
    intro j₀ a _ hsum
    have h1 : ∑ k : s, a k • (k : H i) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul]
      exact hsum
    exact Fintype.linearIndependent_iff.mp hs a h1
  calc s.card = Fintype.card s := (Fintype.card_coe s).symm
    _ ≤ finrank L M := hli.fintype_card_le_finrank

/-- **The Tate–Sen bound** `Σ_{i ∈ J} dim_K H_i ≤ dim_L M`. -/
theorem sum_finrank_le
    (hS : ∀ σ (c : L) y, S σ (c • y) = act σ c • S σ y)
    (hw0 : ∀ σ, w 0 σ = 1) (hwadd : ∀ a b σ, w (a + b) σ = w a σ * w b σ)
    (hT : ∀ i : ℤ, i ≠ 0 → ∀ x : L, (∀ σ, w i σ • act σ x = x) → x = 0)
    (hA : ∀ x : L, (∀ σ, act σ x = x) → ∃ a : K, x = algebraMap K L a)
    (hH : ∀ i, ∀ y ∈ H i, ∀ σ, w i σ • S σ y = y) (J : Finset ℤ) :
    ∑ i ∈ J, finrank K (H i) ≤ finrank L M := by
  classical
  haveI : ∀ i : ℤ, FiniteDimensional K (H i) := fun i =>
    finiteDimensional_twisted act S w H hS hw0 hwadd hT hA hH i
  let d : J → ℕ := fun jj => finrank K (H jj)
  let bv : (Σ jj : J, Fin (d jj)) → M := fun k =>
    ((Module.finBasis K (H k.1) k.2 : H k.1) : M)
  let jf : (Σ jj : J, Fin (d jj)) → ℤ := fun k => k.1
  have hli : LinearIndependent L bv := by
    refine linearIndependent_of_twisted act S w hS hw0 hwadd hT hA jf bv
      (fun k σ => hH _ _ (Module.finBasis K _ k.2).2 σ) ?_
    intro j₀ a ha hs
    by_cases hj₀ : j₀ ∈ J
    · let jj₀ : J := ⟨j₀, hj₀⟩
      have h1 : ∑ m : Fin (d jj₀), a ⟨jj₀, m⟩ • (Module.finBasis K (H jj₀) m) = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero]
        simp only [Submodule.coe_smul]
        rw [← hs, Fintype.sum_sigma, Finset.sum_eq_single jj₀]
        · intro jj _ hjj
          refine Finset.sum_eq_zero fun m _ => ?_
          rw [ha ⟨jj, m⟩ (fun h => hjj (Subtype.ext h)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h2 := Fintype.linearIndependent_iff.mp
        (Module.finBasis K (H jj₀)).linearIndependent _ h1
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
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin, d] at hcard
  rwa [Finset.sum_coe_sort J (fun i => finrank K (H i))] at hcard

end Indep

end

end DeRhamHTMult
