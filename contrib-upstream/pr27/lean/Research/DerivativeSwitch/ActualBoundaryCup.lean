import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The local cochain correction in the actual boundary--cup calculation

The retained Selmer cone is a mapping fibre with third differential
`-loc g + inc u - d q`. A closed degree-one partner therefore satisfies
`inc u = loc g + d q`. The pure-boundary cone product first pairs with
`inc u`, not literally with `loc g`. This module proves the explicit
coboundary correction and its disappearance under a chain trace.

The inputs below are differential/cup Leibniz identities, not a
boundary--duality adjunction. The arithmetic cup maps, global trace square,
and Selmer complexes are identified in the accompanying source application;
they are not constructed in this module. No frozen target is imported.
-/

namespace Research.DerivativeSwitch.ActualBoundaryCup

variable {R L0 L1 L2 T1 T2 : Type*} [CommRing R]
  [AddCommGroup L0] [Module R L0] [AddCommGroup L1] [Module R L1]
  [AddCommGroup L2] [Module R L2] [AddCommGroup T1] [Module R T1]
  [AddCommGroup T2] [Module R T2]

/-- The two local Leibniz identities used at degrees (1,0) and (0,1).
The target differential is the ordinary local cochain differential;
the mapping-fibre differential on a pure local entry is its negative. -/
structure LocalCupData where
  d0 : L0 →ₗ[R] L1
  d1 : L1 →ₗ[R] L2
  dt : T1 →ₗ[R] T2
  cup10 : L1 →ₗ[R] L0 →ₗ[R] T1
  cup01 : L0 →ₗ[R] L1 →ₗ[R] T1
  cup11 : L1 →ₗ[R] L1 →ₗ[R] T2
  cup20 : L2 →ₗ[R] L0 →ₗ[R] T2
  cup02 : L0 →ₗ[R] L2 →ₗ[R] T2
  leibniz10 : ∀ l q, dt (cup10 l q) = cup20 (d1 l) q - cup11 l (d0 q)
  leibniz01 : ∀ q l, dt (cup01 q l) = cup11 (d0 q) l + cup02 q (d1 l)

variable (D : LocalCupData (R := R) (L0 := L0) (L1 := L1)
  (L2 := L2) (T1 := T1) (T2 := T2))

/-- For a closed boundary direction, its cup with `d q` is a negative
coboundary. This is the degree-one sign that must be retained. -/
theorem closed_cup_differential (l : L1) (q : L0) (hl : D.d1 l = 0) :
    D.cup11 l (D.d0 q) = -D.dt (D.cup10 l q) := by
  have h := D.leibniz10 l q
  rw [hl, map_zero, LinearMap.zero_apply, zero_sub] at h
  exact (neg_eq_iff_eq_neg.mp h.symm)

/-- The exact correction between the pure-boundary cone product and the
localization of the global partner. `hcycle` is the actual third cone
cycle equation, not an adjunction assumption. -/
theorem pure_boundary_correction (l localGlobal localCondition : L1) (q : L0)
    (hl : D.d1 l = 0)
    (hcycle : localCondition = localGlobal + D.d0 q) :
    D.cup11 l localCondition =
      D.cup11 l localGlobal - D.dt (D.cup10 l q) := by
  rw [hcycle, map_add, closed_cup_differential D l q hl, sub_eq_add_neg]

/-- Composing the correction with a chain trace gives the boundary--cup
evaluation. Both conditions use the same trace in the arithmetic application. -/
theorem traced_pure_boundary (trace : T2 →ₗ[R] R)
    (htrace : ∀ x, trace (D.dt x) = 0)
    (l localGlobal localCondition : L1) (q : L0)
    (hl : D.d1 l = 0)
    (hcycle : localCondition = localGlobal + D.d0 q) :
    trace (D.cup11 l localCondition) = trace (D.cup11 l localGlobal) := by
  rw [pure_boundary_correction D l localGlobal localCondition q hl hcycle,
    map_sub, htrace, sub_zero]

/-- A local boundary in the first slot has trace zero against a cycle. -/
theorem traced_left_boundary (trace : T2 →ₗ[R] R)
    (htrace : ∀ x, trace (D.dt x) = 0)
    (q : L0) (l : L1) (hl : D.d1 l = 0) :
    trace (D.cup11 (D.d0 q) l) = 0 := by
  have h := D.leibniz01 q l
  rw [hl, map_zero, add_zero] at h
  rw [← h, htrace]

/-- A local boundary in the second slot has trace zero against a cycle. -/
theorem traced_right_boundary (trace : T2 →ₗ[R] R)
    (htrace : ∀ x, trace (D.dt x) = 0)
    (l : L1) (q : L0) (hl : D.d1 l = 0) :
    trace (D.cup11 l (D.d0 q)) = 0 := by
  rw [closed_cup_differential D l q hl, map_neg, htrace, neg_zero]

/-- The local pairing is unchanged by a boundary change in the first slot. -/
theorem traced_change_left (trace : T2 →ₗ[R] R)
    (htrace : ∀ x, trace (D.dt x) = 0)
    (l m : L1) (q : L0) (hm : D.d1 m = 0) :
    trace (D.cup11 (l + D.d0 q) m) = trace (D.cup11 l m) := by
  rw [map_add, LinearMap.add_apply, map_add,
    traced_left_boundary D trace htrace q m hm, add_zero]

/-- The local pairing is unchanged by a boundary change in the second slot. -/
theorem traced_change_right (trace : T2 →ₗ[R] R)
    (htrace : ∀ x, trace (D.dt x) = 0)
    (l m : L1) (q : L0) (hl : D.d1 l = 0) :
    trace (D.cup11 l (m + D.d0 q)) = trace (D.cup11 l m) := by
  rw [map_add, map_add, traced_right_boundary D trace htrace l q hl, add_zero]

end Research.DerivativeSwitch.ActualBoundaryCup
