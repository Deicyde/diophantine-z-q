/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Valuation/Approximation.lean
Original SHA-256: dcd7e49e757007040a4a1d1c2c46d528bb4647d02a8354067c3345a34b9c4c7c
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/Valuation/Approximation.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.AbsoluteValue
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open scoped NNReal WithZero

namespace Valuation

private noncomputable def withZeroMulIntToReal : ℤᵐ⁰ →*₀ ℝ :=
  NNReal.toRealHom.toMonoidWithZeroHom.comp
    (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0))

private theorem withZeroMulIntToReal_strictMono :
    StrictMono withZeroMulIntToReal := by
  intro m n hmn
  exact_mod_cast
    WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2) hmn

-- `AbsoluteValue K ℝ` uses `Real.partialOrder`, while the bundled strict-monotonicity theorem
-- infers `Real.instPreorder`; spell out the propositionally identical comparison needed by the
-- generic constructor to avoid an order-instance diamond.
private theorem withZeroMulIntToReal_monotone {m n : ℤᵐ⁰}
    (hmn : @LE.le ℤᵐ⁰ (@Preorder.toLE ℤᵐ⁰
      (@WithZero.instPreorder (Multiplicative ℤ)
        (@Multiplicative.preorder ℤ Int.instPreorder))) m n) :
    @LE.le ℝ Real.partialOrder.toLE (withZeroMulIntToReal m) (withZeroMulIntToReal n) := by
  exact_mod_cast
    WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2) |>.monotone hmn

section DivisionRing

variable {K : Type*} [DivisionRing K]

/- A `ℤᵐ⁰`-valued valuation, viewed as a real absolute value through the base-two embedding of
its value group. This changes neither comparisons nor equivalence of valuations.

A division ring is needed already here: an `AbsoluteValue` vanishes only at `0`, whereas a
valuation on a general ring may have nontrivial support. -/
noncomputable def toRealAbsoluteValue (v : Valuation K ℤᵐ⁰) : AbsoluteValue K ℝ :=
  @toAbsoluteValue K ℝ ℤᵐ⁰ _ _ _ _ Real.partialOrder (by infer_instance) (by infer_instance) v
    withZeroMulIntToReal
    (fun {_ _} h ↦ withZeroMulIntToReal_monotone h)
    (fun _ ↦ map_eq_zero _)

@[simp]
theorem toRealAbsoluteValue_apply (v : Valuation K ℤᵐ⁰) (x : K) :
    v.toRealAbsoluteValue x =
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) : ℝ) :=
  by simp [toRealAbsoluteValue, withZeroMulIntToReal]

/- Passing a discrete valuation to its real absolute value preserves and reflects inequalities. -/
theorem toRealAbsoluteValue_le_iff (v : Valuation K ℤᵐ⁰) {x y : K} :
    v.toRealAbsoluteValue x ≤ v.toRealAbsoluteValue y ↔ v x ≤ v y := by
  simp only [toRealAbsoluteValue_apply]
  exact withZeroMulIntToReal_strictMono.le_iff_le

/- Passing discrete valuations to real absolute values preserves and reflects equivalence. -/
@[simp]
theorem toRealAbsoluteValue_isEquiv_iff (v w : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsEquiv w.toRealAbsoluteValue ↔ v.IsEquiv w := by
  simp only [AbsoluteValue.IsEquiv, IsEquiv, toRealAbsoluteValue_le_iff]

/- A discrete valuation is nontrivial exactly when its associated real absolute value is. -/
@[simp]
theorem toRealAbsoluteValue_isNontrivial_iff (v : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsNontrivial ↔ v.IsNontrivial := by
  constructor
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mpr hx0, fun hx ↦ hx1 ?_⟩
    rw [toRealAbsoluteValue_apply, hx, map_one, NNReal.coe_one]
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mp hx0, fun hx ↦ hx1 ?_⟩
    rw [toRealAbsoluteValue_apply] at hx
    refine withZeroMulIntToReal_strictMono.injective ?_
    simpa [withZeroMulIntToReal] using hx

end DivisionRing

section Field

variable {K : Type*} [Field K]

/- In the product `(j : ι) → WithAbs (av j)`, the distance from the point `y` of the `i`-th
factor to the `i`-th component of the diagonal image of `x` is `av i (x - y)`. -/
end Field

end Valuation
