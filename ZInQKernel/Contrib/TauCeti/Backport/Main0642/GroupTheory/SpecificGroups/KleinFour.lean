/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.GroupTheory.SpecificGroups.KleinFour), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.GroupTheory.SpecificGroups.KleinFour` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Klein four-groups: transport along isomorphisms, and the product of all elements

Being a Klein four-group, that is having order four and exponent two, is invariant under group
isomorphism. In a commutative Klein four-group `{1, x, y, xy}` the product of all four elements is
`x² y² = 1`.

## Main results

* `MulEquiv.isKleinFour`: a group isomorphic to a Klein four-group is a Klein four-group.
* `IsKleinFour.prod_univ_eq_one`: the product of all elements of a Klein four-group is `1`.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H]

namespace _root_.IsKleinFour

variable {G : Type*} [CommGroup G] [Fintype G] [IsKleinFour G]

/-- **The product of all elements of a Klein four-group is `1`**: they are `1`, `x`, `y` and
`x * y` for any two distinct nonidentity elements `x` and `y`. -/
@[to_additive _root_.IsAddKleinFour.sum_univ_eq_zero
  /-- **The sum of all elements of a Klein four-group is `0`**: they are `0`, `x`, `y` and `x + y`
  for any two distinct nonzero elements `x` and `y`. -/]
theorem prod_univ_eq_one : ∏ g : G, g = 1 := by
  classical
  have : Nontrivial G :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [IsKleinFour.card_four']; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := (Finset.univ : Finset G))
    (s := ({x, 1} : Finset G)) (by
      rw [Finset.card_univ, IsKleinFour.card_four']
      exact (Finset.card_le_two (a := x) (b := 1)).trans_lt (by norm_num : 2 < 4))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  have hxy : x ≠ y := Ne.symm hy.1
  rw [← IsKleinFour.eq_finset_univ hx hy.2 hxy]
  simp [Finset.prod_insert, hx, hy.2, hxy, mul_eq_one_iff_eq_inv, IsKleinFour.inv_eq_self,
    mul_mul_mul_comm x y, IsKleinFour.mul_self]

end _root_.IsKleinFour

end TauCeti
