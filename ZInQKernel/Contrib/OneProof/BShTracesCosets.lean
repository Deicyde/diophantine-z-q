import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-! ON THE SPOT (provenance (c)): reindex the lattice series by cosets before
taking the finite sum. The subtraction in each Weierstrass summand is retained. -/

noncomputable section

namespace BShTraces

open PeriodPair

/-- A coset enumeration of the larger lattice, with representatives using
the sign convention (l-r_i). -/
structure CosetEnumeration (L M : PeriodPair) (ι : Type*) where
  representative : ι → ℂ
  equiv : ι × L.lattice ≃ M.lattice
  coe_equiv (i : ι) (l : L.lattice) :
    (equiv (i, l) : ℂ) = (l : ℂ) - representative i

variable {L M : PeriodPair} {ι : Type*} [Fintype ι] (D : CosetEnumeration L M ι)

/-- Summing the translates relative to their values at the origin gives
the Weierstrass function of the larger lattice. -/
theorem weierstrassP_cosets (z : ℂ) :
    M.weierstrassP z =
      ∑ i, (L.weierstrassP (z + D.representative i) - L.weierstrassP (D.representative i)) := by
  classical
  let f : M.lattice → ℂ := fun l => 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2
  have hs : Summable f := (M.hasSum_weierstrassP z).summable
  change ∑' l, f l = _
  rw [← D.equiv.tsum_eq f]
  change ∑' l, (f ∘ D.equiv) l = _
  rw [(hs.comp_injective D.equiv.injective).tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weierstrassP, weierstrassP, ← Summable.tsum_sub
    (L.hasSum_weierstrassP _).summable (L.hasSum_weierstrassP _).summable]
  apply tsum_congr
  intro l
  have h₁ : z - (D.equiv (i, l) : ℂ) = z + D.representative i - (l : ℂ) := by
    rw [D.coe_equiv]; ring
  have h₂ : (D.equiv (i, l) : ℂ) ^ 2 = (D.representative i - (l : ℂ)) ^ 2 := by
    rw [D.coe_equiv]; ring
  dsimp [f]
  rw [h₁, h₂]
  ring

/-- The same coset enumeration reindexes the convergent inverse power sums.
The term with representative zero recovers the original invariant (G_n). -/
theorem G_cosets {n : ℕ} (hn : 2 < n) :
    M.G n = ∑ i, L.sumInvPow (D.representative i) n := by
  classical
  let f : M.lattice → ℂ := fun l => ((l : ℂ) ^ n)⁻¹
  have hs : Summable f := by
    simpa [f] using (M.hasSum_sumInvPow 0 hn).summable
  change ∑' l, f l = _
  rw [← D.equiv.tsum_eq f]
  change ∑' l, (f ∘ D.equiv) l = _
  rw [(hs.comp_injective D.equiv.injective).tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  apply tsum_congr
  intro l
  simp only [Function.comp_apply, f, D.coe_equiv]

/-- The larger lattice contains every coset representative. -/
theorem representative_mem (i : ι) : D.representative i ∈ M.lattice := by
  have h := (D.equiv (i, 0)).property
  rw [D.coe_equiv, Submodule.coe_zero, zero_sub, neg_mem_iff] at h
  exact h

/-- With a zero representative, the smaller lattice is contained in the larger one. -/
theorem lattice_le (o : ι) (h₀ : D.representative o = 0) : L.lattice ≤ M.lattice := by
  intro z hz
  have h := (D.equiv (o, ⟨z, hz⟩)).property
  rwa [D.coe_equiv, h₀, sub_zero] at h

/-- No other representative lies in the smaller lattice. -/
theorem representative_notMem (o : ι) (h₀ : D.representative o = 0)
    {i : ι} (hi : i ≠ o) : D.representative i ∉ L.lattice := by
  intro hm
  apply hi
  have ht : D.equiv (i, ⟨D.representative i, hm⟩) = D.equiv (o, 0) := by
    apply Subtype.ext
    rw [D.coe_equiv, D.coe_equiv, h₀, Submodule.coe_zero]
    simp
  exact congrArg Prod.fst (D.equiv.injective ht)

/-- The nonzero cosets have an involution that sends each representative
to its negative modulo the smaller lattice. -/
theorem exists_neg_perm (o : ι) (h₀ : D.representative o = 0) :
    ∃ σ : Equiv.Perm {i : ι // i ≠ o},
      ∀ i, D.representative (σ i).val + D.representative i.val ∈ L.lattice := by
  have unique (a : ι) : ∃! b : ι, D.representative b + D.representative a ∈ L.lattice := by
    let r : M.lattice := ⟨D.representative a, representative_mem D a⟩
    let pair := D.equiv.symm r
    have he : (pair.2 : ℂ) - D.representative pair.1 = D.representative a := by
      rw [← D.coe_equiv]
      exact congrArg Subtype.val (D.equiv.apply_symm_apply r)
    have h (b : ι) (hb : D.representative b + D.representative a ∈ L.lattice) :
        D.equiv (b, ⟨_, hb⟩) = r := by
      apply Subtype.ext
      rw [D.coe_equiv]
      change D.representative b + D.representative a - D.representative b = D.representative a
      ring
    refine ⟨pair.1, ?_, fun b hb => congrArg Prod.fst (D.equiv.symm_apply_eq.mpr (h b hb).symm).symm⟩
    have hp : D.representative pair.1 + D.representative a = (pair.2 : ℂ) := by
      linear_combination -he
    change D.representative pair.1 + D.representative a ∈ L.lattice
    rw [hp]
    exact pair.2.property
  let n (i : ι) := (unique i).choose
  have hn (i : ι) : D.representative (n i) + D.representative i ∈ L.lattice :=
    (unique i).choose_spec.1
  have hinv : Function.Involutive n := by
    intro i
    apply ((unique (n i)).choose_spec.2 i ?_).symm
    change D.representative i + D.representative (n i) ∈ L.lattice
    rw [add_comm]
    exact hn i
  have hnode (i : ι) (hi : i ≠ o) : n i ≠ o := by
    intro hh
    have h := hn i
    rw [hh, h₀, zero_add] at h
    exact representative_notMem D o h₀ hi h
  let f (i : {i : ι // i ≠ o}) : {i : ι // i ≠ o} := ⟨n i, hnode i i.property⟩
  have hf : Function.Involutive f := fun i => Subtype.ext (hinv i)
  exact ⟨hf.toPerm f, fun i => hn i⟩

#print axioms weierstrassP_cosets
#print axioms G_cosets
#print axioms representative_mem
#print axioms lattice_le
#print axioms representative_notMem
#print axioms exists_neg_perm

end BShTraces
