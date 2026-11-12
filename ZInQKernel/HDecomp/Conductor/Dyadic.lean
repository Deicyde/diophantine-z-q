import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-conductor/Dyadic.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-conductor: the dyadic unit step of D3 (N5 L828-832)

N5: "the logarithm for `Ĝ_m` identifies `U_F^{e+1}` with `𝔪_F^{e+1}` since `e+1 > e`
[Silverman IV.6.4]. Multiplication by four gives `(U_F^{e+1})^4 = U_F^{3e+1}`."

The direction used is `U_F^{3e+1} ⊆ (U_F^{e+1})^4` (so that `β⁴ = 1` on `U_F` forces `β = 1` on
`U_F^{3e+1}`). We prove both directions for any complete discrete valuation ring `A` with
`v(2) = e`, i.e. `(2) = 𝔪^e`, with no logarithm: a square root of `1 + z`, `z ∈ 𝔪^{2e+s}`,
`s ≥ 1`, is `1 + 2u` with `u² + u = z/4`, a simple root by Hensel's lemma (Mathlib's
`IsAdicComplete.henselianRing`). The ring of integers of a finite extension `F/ℚ₂` with
absolute ramification index `e` satisfies the hypotheses. No `sorry`.
-/

namespace GlueConductor

open IsLocalRing Polynomial

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Square roots near one: if `(2) = 𝔪^e`, `z ∈ 𝔪^{2e+s}` and `s ≥ 1`, then `1 + z = (1 + w)²`
for some `w ∈ 𝔪^{e+s}`. -/
theorem exists_sq_eq_one_add [IsAdicComplete (maximalIdeal A) A] (e s : ℕ) (hs : 1 ≤ s)
    (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (z : A)
    (hz : z ∈ maximalIdeal A ^ (2 * e + s)) :
    ∃ w ∈ maximalIdeal A ^ (e + s), (1 + w) ^ 2 = 1 + z := by
  set m := maximalIdeal A
  -- z = 4c with c ∈ 𝔪^s
  have h4 : m ^ (2 * e + s) = Ideal.span {(4 : A)} * m ^ s := by
    rw [pow_add, two_mul, pow_add, ← h2, Ideal.span_singleton_mul_span_singleton]
    norm_num
  rw [h4, Ideal.mem_span_singleton_mul] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  have hcm : c ∈ m := Ideal.pow_le_self (by omega) hc
  -- Hensel: u² + u = c
  let f : A[X] := X ^ 2 + (X - C c)
  have hmon : f.Monic :=
    (monic_X_pow 2).add_of_left (by rw [degree_X_sub_C, degree_X_pow]; norm_num)
  have heval0 : f.eval 0 ∈ m := by
    simp [f, hcm]
  have hder : IsUnit (Ideal.Quotient.mk m (f.derivative.eval 0)) := by
    simp [f]
  obtain ⟨u, hu, hu0⟩ := HenselianRing.is_henselian f hmon 0 heval0 hder
  rw [sub_zero] at hu0
  have hroot : u ^ 2 + u = c := by
    have := hu.eq_zero
    simp only [f, eval_sub, eval_add, eval_pow, eval_X, eval_C] at this
    linear_combination this
  -- u ∈ 𝔪^s, since u (u + 1) = c and u + 1 is a unit
  have hunit : IsUnit (u + 1) := by
    by_contra h
    have h1 : u + 1 ∈ m := (mem_maximalIdeal _).mpr h
    have : (1 : A) ∈ m := by simpa using sub_mem h1 hu0
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hus : u ∈ m ^ s := by
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have : u = c * v := by
      calc u = u * ((u + 1) * v) := by rw [hv, mul_one]
        _ = (u ^ 2 + u) * v := by ring
        _ = c * v := by rw [hroot]
    rw [this]
    exact Ideal.mul_mem_right _ _ hc
  refine ⟨2 * u, ?_, ?_⟩
  · rw [pow_add, ← h2]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self 2) hus
  · calc (1 + 2 * u) ^ 2 = 1 + 4 * (u ^ 2 + u) := by ring
      _ = 1 + 4 * c := by rw [hroot]

/-- **D3, `U^{3e+1} ⊆ (U^{e+1})⁴`.** In a complete DVR (complete local ring) with `(2) = 𝔪^e`,
every `y ∈ 1 + 𝔪^{3e+1}` is a fourth power of some `x ∈ 1 + 𝔪^{e+1}`. -/
theorem exists_fourth_root [IsAdicComplete (maximalIdeal A) A] (e : ℕ)
    (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (z : A)
    (hz : z ∈ maximalIdeal A ^ (3 * e + 1)) :
    ∃ w ∈ maximalIdeal A ^ (e + 1), (1 + w) ^ 4 = 1 + z := by
  obtain ⟨w₁, hw₁, h₁⟩ := exists_sq_eq_one_add e (e + 1) (by omega) h2 z
    (by rwa [show 2 * e + (e + 1) = 3 * e + 1 by ring])
  obtain ⟨w, hw, h⟩ := exists_sq_eq_one_add e 1 le_rfl h2 w₁
    (by rwa [show 2 * e + 1 = e + (e + 1) by ring])
  exact ⟨w, hw, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, h₁]⟩

/-- **D3, `(U^{e+1})⁴ ⊆ U^{3e+1}`** (the easy direction; no completeness needed). -/
theorem fourth_pow_mem (e : ℕ) (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (w : A)
    (hw : w ∈ maximalIdeal A ^ (e + 1)) :
    (1 + w) ^ 4 - 1 ∈ maximalIdeal A ^ (3 * e + 1) := by
  set m := maximalIdeal A
  have h2m : (2 : A) ∈ m ^ e := h2 ▸ Ideal.mem_span_singleton_self 2
  have hexp : (1 + w) ^ 4 - 1 = 2 * 2 * w + 2 * (3 * w * w) + 2 * 2 * (w * w * w) + w * w * w * w :=
      by
    ring
  rw [hexp]
  have hww : w * w ∈ m ^ (2 * e + 2) := by
    rw [show 2 * e + 2 = (e + 1) + (e + 1) by ring, pow_add]; exact Ideal.mul_mem_mul hw hw
  have h22 : 2 * 2 ∈ m ^ (2 * e) := by rw [two_mul, pow_add]; exact Ideal.mul_mem_mul h2m h2m
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_
  · rw [show 3 * e + 1 = 2 * e + (e + 1) by ring, pow_add]; exact Ideal.mul_mem_mul h22 hw
  · have : 3 * w * w ∈ m ^ (2 * e + 2) := by
      rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hww
    have h' := Ideal.mul_mem_mul h2m this
    rw [← pow_add] at h'
    exact Ideal.pow_le_pow_right (by omega) h'
  · have hwww : w * w * w ∈ m ^ (3 * e + 3) := by
      rw [show 3 * e + 3 = (2 * e + 2) + (e + 1) by ring, pow_add]
      exact Ideal.mul_mem_mul hww hw
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hwww)
  · have : w * w * w * w ∈ m ^ (4 * e + 4) := by
      rw [show 4 * e + 4 = (2 * e + 2) + (2 * e + 2) by ring, pow_add, mul_assoc]
      exact Ideal.mul_mem_mul hww hww
    exact Ideal.pow_le_pow_right (by omega) this

end GlueConductor

