import ZInQKernel.Multiplication.Completeness.AP.LemmaP

/-!
# Field 2′: good slopes with poles at the old primes

Route AP of `docs/research/nt-22p.md`, §3.2 ("The modified completeness argument"). The predicate
`GoodSlopeAP B₀ t` is `GoodSlope B₀ t` with field 2 (`old`) replaced by

> **2′.** For every `ℓ ∈ S_b`, either the bounds of field 2 hold at `ℓ`, or `F(t) > 0` and `t`
> satisfies the hypotheses of Lemma P at `ℓ` (`PoleAbsorbHyp ℓ t`).

Every good slope is a good slope in this sense (`GoodSlope.goodSlopeAP`).
-/

namespace ZInQ.Mult

/-- The bounds of field 2 of `GoodSlope` at one prime `p`. -/
def OldBounds (p : ℕ) (t : ℚ) : Prop :=
  |padicValRat p (t - 1)| ≤ Bp p ∧ |padicValRat p (contactPoly t / (t - 1) ^ 8)| ≤ 8 * Bp p

/-- `GoodSlope` with field 2 replaced by field 2′: at each old prime, either the bounds of
field 2 hold, or `F(t) > 0` and `t` satisfies the hypotheses of Lemma P. -/
structure GoodSlopeAP (B₀ : ℝ) (t : ℚ) : Prop where
  not_mem_contactSet : t ∉ contactSet
  ne_one : t ≠ 1
  old : ∀ p ∈ S_b, OldBounds p t ∨ (0 < contactPoly t ∧ PoleAbsorbHyp p t)
  contact : ∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p →
    B₀ < p ∧ GoodSlopePrime p ∧
      ∀ c ∈ contactSet, 0 < padicValRat p (t - c) → padicValRat p (t - c) = 1
  few : ∃ P : Finset ℕ, P.card ≤ 6 ∧ ∀ p, p ∈ P ↔ p ∉ S_b ∧ IsOddContactPrime t p

/-- **Field 2 implies field 2′**: every good slope satisfies `GoodSlopeAP`. -/
theorem GoodSlope.goodSlopeAP {B₀ : ℝ} {t : ℚ} (ht : GoodSlope B₀ t) : GoodSlopeAP B₀ t :=
  ⟨ht.not_mem_contactSet, ht.ne_one, fun p hp => Or.inl (ht.old p hp), ht.contact, ht.few⟩

/-- At an odd contact prime `p ∉ S_b` of a slope satisfying 2′, `v_p(F(t)/(t-1)⁸) = 1` and
`v_p(t - 1) = 0` (the argument of `padicValRat_contactQuot_eq_one`, which uses only fields 1
and 3). -/
theorem GoodSlopeAP.contactQuot_eq_one {B₀ : ℝ} {t : ℚ} (ht : GoodSlopeAP B₀ t) {p : ℕ}
    (hpS : p ∉ S_b) (hodd : IsOddContactPrime t p) :
    padicValRat p (contactPoly t / (t - 1) ^ 8) = 1 ∧ padicValRat p (t - 1) = 0 := by
  have hp := hodd.1
  have : Fact p.Prime := ⟨hp⟩
  have hp61 : 61 < p := by have := le_of_not_mem_S_b hp hpS; omega
  obtain ⟨-, -, hone⟩ := ht.contact p hpS hodd
  obtain ⟨-, c₀, hc₀, hpos, -⟩ := hodd
  have h1 := hone c₀ hc₀ hpos
  have hother : ∀ c ∈ insert 1 contactSet, c ≠ c₀ → padicValRat p (t - c) = 0 := by
    intro c hc hne
    have hd := padicValRat_contact_diff hp61 (Finset.mem_insert_of_mem hc₀) hc hne.symm
    have hd0 : c₀ - c ≠ 0 := sub_ne_zero.mpr hne.symm
    have ht0 : t - c₀ ≠ 0 := by intro h; rw [h] at h1; simp at h1
    have hsum : (c₀ - c) + (t - c₀) ≠ 0 := by
      intro h
      have : t = c := by linarith
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact ht.ne_one this
      · exact ht.not_mem_contactSet (by rw [this]; exact hc')
    have e : t - c = (c₀ - c) + (t - c₀) := by ring
    rw [e, padicValRat.add_eq_of_lt hsum hd0 ht0 (by rw [hd, h1]; norm_num), hd]
  have ht1 : padicValRat p (t - 1) = 0 := by
    have : (1 : ℚ) ≠ c₀ := fun h => by
      rw [← h] at hc₀
      simp [contactSet] at hc₀
      norm_num at hc₀
    exact hother 1 (Finset.mem_insert_self _ _) this
  refine ⟨?_, ht1⟩
  rw [padicValRat_contactQuot ht.not_mem_contactSet ht.ne_one, ht1,
    Finset.sum_eq_single c₀ (fun c hc hne => hother c (Finset.mem_insert_of_mem hc) hne)
      (fun h => absurd hc₀ h), h1]
  norm_num

end ZInQ.Mult
