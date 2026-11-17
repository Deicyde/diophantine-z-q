/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Valuation/AbsoluteValue.lean
Original SHA-256: 8551dc4f4249165a2ddb5e132947cdccb3f77285e7931b350a7479d94f7c022f
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
TauCeti/RingTheory/Valuation/AbsoluteValue.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.RingTheory.Valuation.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open MonoidWithZeroHom

namespace Valuation

section AbsoluteValue

variable {K S Γ₀ : Type*} [DivisionRing K] [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]
  [Semiring S] [PartialOrder S] [addLeftMono : AddLeftMono S] [addRightMono : AddRightMono S]

omit [Nontrivial Γ₀] in
private theorem comp_apply_add_le_add_of_monotone (v : _root_.Valuation K Γ₀)
    (f : Γ₀ →*₀ S) (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (x y : K) :
    f (v (x + y)) ≤ f (v x) + f (v y) := by
  refine (hf (v.map_add x y)).trans ?_
  rcases le_total (v x) (v y) with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left <| by rw [← map_zero f]; exact hf zero_le
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right <| by rw [← map_zero f]; exact hf zero_le

/- Compose a valuation with a monotone, zero-reflecting monoid-with-zero homomorphism to obtain
an absolute value. -/
noncomputable def toAbsoluteValue (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0) :
    AbsoluteValue K S :=
  AbsoluteValue.mk (f.comp v.toMonoidWithZeroHom)
    (fun x ↦ by rw [← map_zero f]; exact hf zero_le)
    (fun x ↦ by
      -- `AbsoluteValue.mk` has no evaluation lemma available while constructing the value.
      change f (v x) = 0 ↔ x = 0
      rw [hf_zero]
      exact v.zero_iff)
    (comp_apply_add_le_add_of_monotone v f hf)

include addLeftMono addRightMono in
/- Evaluation of the absolute value obtained by composing a valuation with a monotone,
zero-reflecting monoid-with-zero homomorphism. -/
@[simp]
theorem toAbsoluteValue_apply (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0) (x : K) :
    v.toAbsoluteValue f hf hf_zero x = f (v x) := by
  -- Unfold the constructor once to establish the public evaluation lemma used below.
  change (f.comp v.toMonoidWithZeroHom) x = f (v x)
  rfl

include addLeftMono addRightMono in
/- If one input has no larger valuation than another, their sum has absolute value at most that
of the latter. -/
theorem toAbsoluteValue_add_le_right (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0)
    {x y : K} (h : v x ≤ v y) :
    v.toAbsoluteValue f hf hf_zero (x + y) ≤ v.toAbsoluteValue f hf hf_zero y := by
  rw [toAbsoluteValue_apply, toAbsoluteValue_apply]
  exact hf ((v.map_add x y).trans_eq (max_eq_right h))

end AbsoluteValue

section IsNonarchimedean

variable {K S Γ₀ : Type*} [DivisionRing K] [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]
  [Semiring S] [LinearOrder S] [addLeftMono : AddLeftMono S] [addRightMono : AddRightMono S]

/- An absolute value obtained from a valuation through a monotone realization is
nonarchimedean. -/
theorem isNonarchimedean_toAbsoluteValue (v : _root_.Valuation K Γ₀) (f : Γ₀ →*₀ S)
    (hf : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) (hf_zero : ∀ a, f a = 0 ↔ a = 0) :
    IsNonarchimedean (v.toAbsoluteValue f hf hf_zero) := by
  intro x y
  rcases le_total (v x) (v y) with h | h
  · rw [max_eq_right (by simpa only [toAbsoluteValue_apply] using hf h)]
    exact v.toAbsoluteValue_add_le_right f hf hf_zero h
  · rw [max_eq_left (by simpa only [toAbsoluteValue_apply] using hf h)]
    simpa only [add_comm] using
      v.toAbsoluteValue_add_le_right f hf hf_zero (x := y) (y := x) h

end IsNonarchimedean

end Valuation
