import ZInQKernel.RouteK.Selmer.Good
import ZInQKernel.RouteK.Selmer.Bits

/-!
# Proposition 0 (nt-prop0 §2.7, file 9 of §4.1)

For squarefree `d ≡ 5 (mod 8)`, the explicit system `Σ(𝒞_d)` (`natConfig d _`) describes
`Sel₂(C_d)` exactly:

* `prop0`: `σ` solves `Σ(𝒞_d)` iff `(a(σ), b(σ)) = selPair d σ ∈ Sel2 d`. This assembles the
  real place (`loc_real_selPair_iff`), the place 2 (`loc_two_selPair_iff_D`, Lemma T), the odd
  primes `p ∣ d` (`loc_padic_selPair_iff_rows`, Lemma B) and the odd primes `p ∤ d`
  (`loc_padic_good_of_units`, Lemma G2, with `not_dvd_selPair`); the assembly itself is
  `isSol_iff_selPair_mem_of_G2` (Bits.lean).
* `sel2_subset_range_selPair`: every element of `Sel2 d` is `selPair d σ` (by Lemma G1 in the form
  `loc_padic_good_iff`, no odd prime outside `d` divides a Selmer pair; the sign and the place 2
  are the remaining unknowns).
* `prop0Statement`, and `certifiedRank_of_certifiedRankSel : CertifiedRankSel → CertifiedRank`.
-/

namespace ZInQ.RouteK.Selmer

/-- **Proposition 0, first half.** For squarefree `d ≡ 5 (mod 8)`, `σ` solves `Σ(𝒞_d)` iff
`(a(σ), b(σ)) ∈ Sel₂(C_d)`. -/
theorem prop0 {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d) (σ : Unknowns d.primeFactors) :
    (natConfig d (odd_of_mod_eight_eq_five hd5)).IsSol σ ↔ selPair d σ ∈ Sel2 d :=
  isSol_iff_selPair_mem_of_G2 hd5 hsq
    (fun _ _ hp2 hpd _ _ ha hb => loc_padic_good_of_units hp2 hpd ha hb) σ

/-- Raising the exponent of 2 in `classInt` doubles it. -/
theorem classInt_one_eq_two_mul (d : ℕ) (e₀ : ZMod 2) (w : d.primeFactors → ZMod 2) :
    classInt d e₀ 1 w = 2 * classInt d e₀ 0 w := by
  simp only [classInt, show (1 : ZMod 2).val = 1 from rfl, ZMod.val_zero, pow_one, pow_zero]
  ring

/-- An odd squarefree integer all of whose prime factors divide `d` divides `d`. -/
theorem dvd_of_squarefree_of_odd_primes_dvd {d : ℕ} (hd0 : d ≠ 0) {a : ℤ} (hsq : Squarefree a)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → p ∣ d) : a ∣ (d : ℤ) := by
  have hn : Squarefree a.natAbs := Int.squarefree_natAbs.mpr hsq
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast,
    ← Nat.prod_primeFactors_of_squarefree hn, Nat.prod_primeFactors_dvd_iff hd0]
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp'.1, h p hp'.1 (Int.natCast_dvd.mpr hp'.2.1), hd0⟩

/-- A squarefree integer with no odd prime factor outside `d` (`d` odd) is a value of
`classInt d`. -/
theorem exists_classInt_eq {d : ℕ} (hd : Odd d) {a : ℤ} (hsq : Squarefree a)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ∣ d → ¬(p : ℤ) ∣ a) :
    ∃ e₀ e₁ w, classInt d e₀ e₁ w = a := by
  have hd0 : d ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hd)
  have hodd : ∀ {c : ℤ}, Squarefree c → ¬(2 : ℤ) ∣ c → (∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ∣ d →
      ¬(p : ℤ) ∣ c) → ∃ e₀ w, classInt d e₀ 0 w = c := by
    intro c hc h2 hc'
    have hcd : c ∣ (d : ℤ) := dvd_of_squarefree_of_odd_primes_dvd hd0 hc fun p hp hpc => by
      by_contra hpd
      by_cases hp2 : p = 2
      · subst hp2; exact h2 (by exact_mod_cast hpc)
      · exact hc' p hp hp2 hpd hpc
    have h1 : (natClass d c).2.1 = 0 := by
      have := classInt_natClass hd0 hc hcd
      rcases zmod2_cases (natClass d c).2.1 with h0 | h0
      · exact h0
      · exfalso; apply h2
        rw [← this, two_dvd_classInt_iff hd]; exact h0
    refine ⟨(natClass d c).1, (natClass d c).2.2, ?_⟩
    rw [← h1]; exact classInt_natClass hd0 hc hcd
  by_cases h2 : (2 : ℤ) ∣ a
  · obtain ⟨c, rfl⟩ := h2
    have hc : Squarefree c := hsq.of_mul_right
    have hc2 : ¬(2 : ℤ) ∣ c := by
      rintro ⟨e, rfl⟩
      have := hsq 2 ⟨e, by ring⟩
      exact absurd (Int.isUnit_iff.mp this) (by omega)
    obtain ⟨e₀, w, hw⟩ := hodd hc hc2 fun p hp hp2 hpd hpc =>
      h p hp hp2 hpd (Dvd.dvd.mul_left hpc 2)
    exact ⟨e₀, 1, w, by rw [classInt_one_eq_two_mul, hw]⟩
  · obtain ⟨e₀, w, hw⟩ := hodd hsq h2 h
    exact ⟨e₀, 0, w, hw⟩

/-- **Proposition 0, second half (onto).** Every element of `Sel₂(C_d)` is `(a(σ), b(σ))` for
some unknowns `σ`. Only `d` odd is needed. -/
theorem sel2_subset_range_selPair {d : ℕ} (hd : Odd d) : Sel2 d ⊆ Set.range (selPair d) := by
  rintro ⟨a, b⟩ ⟨ha, hb, -, hloc⟩
  have hgood : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ∣ d → ¬(p : ℤ) ∣ a ∧ ¬(p : ℤ) ∣ b :=
    fun p hp hp2 hpd => by
      have := Fact.mk hp
      exact (loc_padic_good_iff hp2 hpd ha hb).mp (hloc p)
  obtain ⟨e₀, e₁, w, hw⟩ := exists_classInt_eq hd ha fun p hp hp2 hpd => (hgood p hp hp2 hpd).1
  obtain ⟨f₀, f₁, w', hw'⟩ := exists_classInt_eq hd hb fun p hp hp2 hpd => (hgood p hp hp2 hpd).2
  exact ⟨⟨e₀, e₁, f₀, f₁, w, w'⟩, by simp only [selPair, hw, hw']⟩

/-- **Proposition 0** in the form `certifiedRank_of_sel` uses (`Prop0Statement`). -/
theorem prop0Statement : Prop0Statement := fun _ hd5 hsq =>
  ⟨prop0 hd5 hsq, sel2_subset_range_selPair (odd_of_mod_eight_eq_five hd5)⟩

/-- **CR₃ from CR₃^Sel.** The hypothesis `CertifiedRankSel` (stated on `Sel₂(C_d)` itself, see its
docstring) implies `ZInQ.CertifiedRank` (stated on the explicit system `Σ(𝒞_d)`), by
Proposition 0. -/
theorem certifiedRank_of_certifiedRankSel (hCRS : CertifiedRankSel) : CertifiedRank :=
  certifiedRank_of_sel hCRS prop0Statement

end ZInQ.RouteK.Selmer
