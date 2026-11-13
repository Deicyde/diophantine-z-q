/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.Algebra.Group.PowMonoidHom), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.Algebra.Group.PowMonoidHom`.
module

public import ZInQKernel.Contrib.TauCeti.Algebra.Group.PowMonoidHom
public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.NormNum

public section

namespace TauCeti

/-- In a commutative group all of whose elements satisfy `y ^ n = 1`, the `d`-th powers are
exactly the `gcd(n, d)`-th powers. For a group of order `N` this applies with `n = N` (Mathlib's
`pow_card_eq_one'`). -/
@[to_additive /-- In an additive commutative group all of whose elements satisfy `n • y = 0`, the
`d`-th multiples are exactly the `gcd(n, d)`-th multiples. -/]
theorem range_powMonoidHom_gcd {G : Type*} [CommGroup G] {n : ℕ} (hn : ∀ y : G, y ^ n = 1)
    (d : ℕ) : (powMonoidHom (n.gcd d) : G →* G).range = (powMonoidHom d : G →* G).range := by
  refine le_antisymm ?_ ?_
  -- Bézout: writing `gcd(n, d) = n * a + d * b`, `y ^ gcd(n, d) = (y ^ b) ^ d` as `y ^ n = 1`.
  · rintro _ ⟨y, rfl⟩
    refine ⟨y ^ n.gcdB d, ?_⟩
    have ha : y ^ ((n : ℤ) * n.gcdA d) = 1 := by simp [zpow_mul, hn]
    have hb : (y ^ n.gcdB d) ^ d = y ^ ((d : ℤ) * n.gcdB d) := by
      rw [mul_comm, zpow_mul, zpow_natCast]
    simp only [powMonoidHom_apply, hb, ← zpow_natCast y (n.gcd d), Nat.gcd_eq_gcd_ab, zpow_add,
      ha, one_mul]
  -- Every `d`-th power is a `gcd(n, d)`-th power since `gcd(n, d)` divides `d`.
  · rintro _ ⟨y, rfl⟩
    refine ⟨y ^ (d / n.gcd d), ?_⟩
    rw [powMonoidHom_apply, powMonoidHom_apply, ← pow_mul,
      Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]

end TauCeti

end
