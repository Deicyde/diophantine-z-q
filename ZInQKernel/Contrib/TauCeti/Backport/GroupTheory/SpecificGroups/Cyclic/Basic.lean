/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

section
namespace TauCeti

/-- Summing a function over the powers `1, g, …, gⁿ⁻¹` of a generator of a finite cyclic group
is the sum over the whole group, where `n = orderOf g`. -/
theorem sum_range_orderOf_eq_sum {G M : Type*} [Group G] [Fintype G] [AddCommMonoid M]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (f : G → M) :
    ∑ i ∈ Finset.range (orderOf g), f (g ^ i) = ∑ x : G, f x := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply, finEquivZPowers_apply] using
    (((finEquivZPowers (isOfFinOrder_of_finite g)).trans
      (Equiv.subtypeUnivEquiv hg)).sum_comp f)

end TauCeti
end

end
