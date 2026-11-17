/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Valuation/Discrete/Order.lean
Original SHA-256: 89aaa995f5d6446b9aebe38f29bc0d9bcb318425c04c9e7e03dae71c8c784315
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/Valuation/Discrete/Order.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Valuation.Discrete.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open scoped WithZero

open MonoidWithZeroHom

namespace Valuation

variable {F : Type*} [Field F]

/- The additive order attached to a `ℤᵐ⁰`-valued valuation, with the convention that a
uniformizer has order one.  It has the junk value `ord_v 0 = 0`. -/
noncomputable def ord (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ℤ :=
  -WithZero.log (v f)

theorem ord_def (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v f = -WithZero.log (v f) :=
  (rfl)

/- The order function commutes with restriction along a ring homomorphism. -/
theorem valuation_eq_exp_neg_ord (v : _root_.Valuation F ℤᵐ⁰) {f : F} (hf : f ≠ 0) :
    v f = WithZero.exp (-ord v f) := by
  rw [ord_def, neg_neg, WithZero.exp_log (v.ne_zero_iff.mpr hf)]

theorem ord_eq_iff_valuation_eq_exp_neg (v : _root_.Valuation F ℤᵐ⁰) {f : F}
    (hf : f ≠ 0) {n : ℤ} : ord v f = n ↔ v f = WithZero.exp (-n) := by
  rw [valuation_eq_exp_neg_ord v hf, WithZero.exp_inj, neg_inj]

@[simp]
theorem ord_zero (v : _root_.Valuation F ℤᵐ⁰) : ord v 0 = 0 := by
  simp [ord_def]

theorem ord_mul (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f * g) = ord v f + ord v g := by
  rw [ord_def, ord_def, ord_def, map_mul,
    WithZero.log_mul (v.ne_zero_iff.mpr hf) (v.ne_zero_iff.mpr hg)]
  ring

@[simp]
theorem ord_inv (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v f⁻¹ = -ord v f := by
  simp [ord_def, map_inv₀, WithZero.log_inv]

@[simp]
theorem ord_zpow (v : _root_.Valuation F ℤᵐ⁰) (f : F) (n : ℤ) :
    ord v (f ^ n) = n * ord v f := by
  simp [ord_def, map_zpow₀, WithZero.log_zpow, mul_neg]

theorem ord_div (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f / g) = ord v f - ord v g := by
  rw [div_eq_mul_inv, ord_mul v hf (inv_ne_zero hg), ord_inv, sub_eq_add_neg]

theorem ord_div_zpow (v : _root_.Valuation F ℤᵐ⁰) {f t : F} (hf : f ≠ 0) (ht : t ≠ 0)
    (n : ℤ) : ord v (f / t ^ n) = ord v f - n * ord v t := by
  rw [ord_div v hf (zpow_ne_zero _ ht), ord_zpow]

/- **A surjective valuation onto `ℤᵐ⁰` is nontrivial.** Surjectivity is the form the hypothesis
usually arrives in — a `Place` carries it by definition — while the results about order and
normalization are stated for a nontrivial valuation, and this converts one to the other. -/
theorem ord_surjective (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) :
    Function.Surjective (ord v) := fun n => by
  obtain ⟨f, hf⟩ := hv (WithZero.exp (-n))
  have hf0 : f ≠ 0 := v.ne_zero_iff.mp (by simp [hf])
  exact ⟨f, (ord_eq_iff_valuation_eq_exp_neg v hf0).mpr hf⟩

theorem mem_valuationSubring_iff_ord_nonneg (v : _root_.Valuation F ℤᵐ⁰) {f : F} :
    f ∈ v.valuationSubring ↔ 0 ≤ ord v f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [_root_.Valuation.mem_valuationSubring_iff,
      valuation_eq_exp_neg_ord v hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

section ValueGroup

variable {F : Type*} [Ring F]

/- Surjectivity of `v` makes its value group the whole of `ℤᵐ⁰`. -/
theorem valueGroup_eq_top_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : v.valueGroup = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun γ => mem_valueGroup _ (hv γ)

/- A surjective `ℤᵐ⁰`-valued valuation has nontrivial value group. -/
theorem nontrivial_valueGroup_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : Nontrivial v.valueGroup := by
  rw [valueGroup_eq_top_of_surjective v hv]
  exact (Subgroup.topEquiv (G := ℤᵐ⁰ˣ)).toEquiv.nontrivial

end ValueGroup

variable {F : Type*} [Field F]

/- The valuation ring of a surjective `ℤᵐ⁰`-valued valuation is a DVR. -/
theorem valuationSubring_isDiscreteValuationRing_of_surjective
    (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) :
    IsDiscreteValuationRing v.valuationSubring := by
  let _ := nontrivial_valueGroup_of_surjective v hv
  exact _root_.Valuation.valuationSubring_isDiscreteValuationRing v

/- Uniformizers of a surjective `ℤᵐ⁰`-valuation are exactly the elements of order one. -/
theorem IsEquiv.ord_nonneg_iff {v w : _root_.Valuation F ℤᵐ⁰} (h : v.IsEquiv w)
    (f : F) : 0 ≤ ord v f ↔ 0 ≤ ord w f := by
  rw [← mem_valuationSubring_iff_ord_nonneg v, ← mem_valuationSubring_iff_ord_nonneg w,
    _root_.Valuation.mem_valuationSubring_iff, _root_.Valuation.mem_valuationSubring_iff]
  exact h.le_one_iff_le_one

/- **Equivalent valuations agree on which elements have order zero.** This is the additive-order
analogue of `Valuation.IsEquiv.eq_one_iff_eq_one`: away from `0`, order zero says the valuation is
`1`, so the two valuations have the same units. The junk value `ord v 0 = 0` is absorbed on both
sides.

Only equivalence is needed; neither valuation has to be surjective. -/
theorem IsEquiv.ord_eq_zero_iff {v w : _root_.Valuation F ℤᵐ⁰} (h : v.IsEquiv w)
    (f : F) : ord v f = 0 ↔ ord w f = 0 := by
  -- Nonnegativity at `f` and at `f⁻¹` together pin the order to zero, and `ord_inv` turns the
  -- second into nonpositivity at `f`.
  have hf := h.ord_nonneg_iff f
  have hinv := h.ord_nonneg_iff f⁻¹
  rw [ord_inv, ord_inv] at hinv
  omega

/- Two equivalent normalized `ℤᵐ⁰`-valuations are equal. -/
theorem eq_of_isEquiv_of_surjective {v w : _root_.Valuation F ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  have hmem := h.ord_nonneg_iff
  have hzero := h.ord_eq_zero_iff
  -- Choose order-one elements for both normalized valuations and compare their orders.
  obtain ⟨t, ht⟩ := ord_surjective v hv 1
  obtain ⟨s, hs⟩ := ord_surjective w hw 1
  have ht0 : t ≠ 0 := fun h' => by simp [h'] at ht
  have hs0 : s ≠ 0 := fun h' => by simp [h'] at hs
  have htW : 1 ≤ ord w t := by
    have h₁ := (hmem t).mp (by omega)
    have h₂ := (hzero t).not.mp (by omega)
    omega
  have hsV : 1 ≤ ord v s := by
    have h₁ := (hmem s).mpr (by omega)
    have h₂ := (hzero s).not.mpr (by omega)
    omega
  -- Dividing `s` by the appropriate power of `t` has order zero for both valuations;
  -- this forces the chosen `v`-uniformizer `t` to have `w`-order one.
  have hone : ord w t = 1 := by
    have hst : ord v (s / t ^ ord v s) = 0 := by
      rw [ord_div_zpow v hs0 ht0, ht]
      ring
    have hW := (hzero _).mp hst
    rw [ord_div_zpow w hs0 ht0, hs] at hW
    nlinarith [htW, hsV]
  -- Removing the `v`-order of an arbitrary nonzero element now shows that both orders,
  -- and hence both valuations, agree pointwise.
  refine _root_.Valuation.ext fun f => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have key : ord w f = ord v f := by
    have h₀ : ord v (f / t ^ ord v f) = 0 := by
      rw [ord_div_zpow v hf ht0, ht]
      ring
    have hW := (hzero _).mp h₀
    rw [ord_div_zpow w hf ht0, hone] at hW
    omega
  rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord w hf, key]

end Valuation
