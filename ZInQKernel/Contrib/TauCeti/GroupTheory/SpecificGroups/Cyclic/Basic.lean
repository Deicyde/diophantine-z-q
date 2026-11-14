/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Vendored from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 5a01f5fe3621, module TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic), Apache-2.0.
-- Modified for the Z-in-Q kernel: IsCyclic.mem_range_powMonoidHom_iff removed (task stab-clash: the vendored commit-97a5b235 module ZInQKernel.Contrib.TauCeti.GroupTheory.SpecificGroups.Cyclic.PowMonoidHom declares that name with a more general statement, as Tau Ceti did at commit 97a5b235; its one user, FieldTheory/Finite/EulerCriterion.lean, now uses that version).
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic groups

For `n ≠ 0`, this file gives the standard computable enumeration of
`Multiplicative (ZMod n)`, transported from the additive group `ZMod n`.
It also records that an element corresponding to `1` under an equivalence with
`Multiplicative ℤ` generates its group. (Euler's criterion for `n`-th powers in a finite cyclic
group, `IsCyclic.mem_range_powMonoidHom_iff`, is in `Cyclic/PowMonoidHom.lean`.)

## Main definitions

* `TauCeti.cyclicElements`: a computable enumeration of `Multiplicative (ZMod n)`.

## Main results

* `TauCeti.mem_cyclicElements`: the enumeration exhausts the group when `n ≠ 0`.
* `MulEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one`: an element sent to `1` by an equivalence with
  `Multiplicative ℤ` generates its group.

## References

The construction follows the enumeration pattern of `TauCeti.dihedralElements`.
-/

public section

namespace TauCeti

/-- For `n ≠ 0`, the standard computable enumeration of the finite cyclic group
`Multiplicative (ZMod n)`. For `n = 0`, this list is empty. -/
@[expose] def cyclicElements (n : ℕ) : List (Multiplicative (ZMod n)) :=
  List.ofFn fun i : Fin n => Multiplicative.ofAdd (i : ZMod n)

/-- Every element of `Multiplicative (ZMod n)` occurs in `TauCeti.cyclicElements n` when `n` is
nonzero. -/
theorem mem_cyclicElements (n : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) :
    g ∈ cyclicElements n := by
  rw [cyclicElements, List.mem_ofFn']
  exact ⟨⟨g.toAdd.val, ZMod.val_lt g.toAdd⟩,
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val g.toAdd)⟩

/-- An element sent to `1` by a group equivalence with `Multiplicative ℤ` generates its
group. -/
theorem _root_.MulEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one {G : Type*} [Group G] {g : G}
    (e : G ≃* Multiplicative ℤ) (hg : e g = Multiplicative.ofAdd 1) :
    Subgroup.zpowers g = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun y => ⟨(e y).toAdd,
    e.injective (by simp [hg, ← ofAdd_zsmul])⟩

end TauCeti
