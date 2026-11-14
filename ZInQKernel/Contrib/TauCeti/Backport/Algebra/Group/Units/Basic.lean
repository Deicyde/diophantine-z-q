/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.Algebra.Group.Units.Basic), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.Algebra.Group.Units.Basic` (task t40-tate).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten;
-- TauCeti.mem_range_iff_exists_units_map_eq, Units.val_mul_zpow_natCast_mul and
-- Units.val_mul_zpow_neg_natCast_succ_mul removed (task t40-clash: same names as declarations of the vendored
-- ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic, now imported instead).
module

public import ZInQKernel.Contrib.TauCeti.Algebra.Group.Units.Basic
-- Provides `Units.val_mul_zpow_natCast_mul`, `Units.val_mul_zpow_neg_natCast_succ_mul` and
-- `TauCeti.mem_range_iff_exists_units_map_eq` (for groups with zero), used downstream (task t40-clash).
public import ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Units.Hom

import Mathlib.Algebra.Group.Commute.Units

/-!
# Units in monoids

This file records that an element conjugated by a unit into an element commuting with that unit
is that element.

The Tau Ceti module also lifts units in the range of a local monoid homomorphism and rewrites
integer powers of products of units as monomials with consecutive natural exponents
(`TauCeti.mem_range_iff_exists_units_map_eq`, `Units.val_mul_zpow_natCast_mul`,
`Units.val_mul_zpow_neg_natCast_succ_mul`). In this kernel those three names are already
declared, for groups with zero, by the vendored
`ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic`, which this file imports; the
monoid generalizations are omitted so that both modules can be imported together.

## Main results

* `Units.eq_of_mul_mul_inv_eq_of_commute`: if the conjugate of `a` by a unit `u` is an element
  commuting with `u`, then `a` equals it.
-/

public section

namespace Units

/-- If the conjugate of `a` by a unit `u` is an element `z` that commutes with `u`, then `a = z`. -/
theorem eq_of_mul_mul_inv_eq_of_commute {A : Type*} [Monoid A] {a z : A} (u : Aˣ)
    (h : (u : A) * a * ↑u⁻¹ = z) (hz : Commute z u) : a = z := by
  calc a = ↑u⁻¹ * ((u : A) * a * ↑u⁻¹) * u := by simp [mul_assoc]
    _ = z := by rw [h, mul_assoc, hz.eq, Units.inv_mul_cancel_left]

end Units
