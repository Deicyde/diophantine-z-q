import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
# Local conjugation for the actual twisted coefficient representation

The coefficient transport is derived from `T(frobenius) = T(tau)`, rather than
assumed scalar. All identities hold over a commutative ring, including finite
Artin rings at two. Raw conjugation takes values in the conjugate coefficient
system; it does not insert the coefficient involution a second time.

The arithmetic occurrence of the data (including the common tame quotient) is
specified and reviewed separately in `research/conjugate-local-transport/`.
This module does not construct Galois/Selmer complexes or global duality.
-/

namespace Research.DerivativeSwitch.ConjugateLocalTransport

variable {R G V : Type*} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V]

/-- The actual scalar twist of a representation restricted to a subgroup. -/
def twist (H : Subgroup G) (T : G →* Module.End R V) (alpha : H →* Rˣ) :
    H →* Module.End R V where
  toFun h := (alpha h : R) • T (h : G)
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp [Module.End.mul_apply, mul_smul]
    exact smul_comm _ _ _

/-- Conjugation on a normal subgroup, preserving the coefficient-system type. -/
def conjugation (H : Subgroup G) [H.Normal] (a : G) : H →* H where
  toFun h := ⟨a * (h : G) * a⁻¹, (inferInstance : H.Normal).conj_mem h h.2 a⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; simp [mul_assoc]

/-- The crossed-cocycle equation, with the coefficient action visible. -/
def IsCrossed (rho : G →* Module.End R V) (p : G → V) : Prop :=
  ∀ g h, p (g * h) = p g + rho g (p h)

theorem crossed_conjugation (rho : G →* Module.End R V) (p : G → V)
    (hp : IsCrossed rho p) (a x : G) :
    p (a⁻¹ * x * a) = rho a⁻¹ (p x + rho x (p a) - p a) := by
  have h := hp a (a⁻¹ * x * a)
  have ha : a * (a⁻¹ * x * a) = x * a := by group
  rw [ha, hp x a] at h
  have hh : rho a (p (a⁻¹ * x * a)) = p x + rho x (p a) - p a := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using h.symm
  have hh' := congrArg (rho a⁻¹) hh
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] using hh'

theorem crossed_pow_of_trivial (rho : G →* Module.End R V) (p : G → V)
    (hp : IsCrossed rho p) (x : G) (hx : rho x = 1) (n : ℕ) :
    p (x ^ n) = (n : R) • p x := by
  have hzero : p 1 = 0 := by
    have h := hp 1 1
    simpa using h
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [pow_succ', hp, hx, Module.End.one_apply, ih, Nat.cast_add, Nat.cast_one,
      add_smul, one_smul, add_comm]

/-- Only source representation/group data are stored. No scalar-transport or
normalized-coordinate equation is a field of this structure. -/
structure LocalData (H : Subgroup G) (T : G →* Module.End R V)
    (alpha : H →* Rˣ) where
  tau : G
  frobenius : G
  transporter : H
  finiteGenerator : H
  inertia : H
  ell : ℕ
  tau_sq : tau ^ 2 = 1
  frobenius_eq : frobenius = (transporter : G) * tau
  tate_frobenius : T frobenius = T tau
  finite_eq : (finiteGenerator : G) = frobenius ^ 2
  tame_eq : frobenius * (inertia : G) * frobenius⁻¹ = (inertia : G) ^ ell
  alpha_finite : alpha finiteGenerator = 1
  alpha_inertia : alpha inertia = 1
  tate_inertia : T (inertia : G) = 1

namespace LocalData

variable {H : Subgroup G} {T : G →* Module.End R V} {alpha : H →* Rˣ}
  (D : LocalData H T alpha)

/-- A single explicit integral unit, common to every cocycle on these data. -/
def transportUnit : Rˣ := (alpha D.transporter)⁻¹

def coordinates (p : H → V) : V × V := (p D.finiteGenerator, p D.inertia)

theorem tate_transporter : T (D.transporter : G) = 1 := by
  have h := D.tate_frobenius
  rw [D.frobenius_eq, map_mul] at h
  have h' := congrArg (fun f => f * T D.tau⁻¹) h
  simpa only [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] using h'

theorem twist_transporter : twist H T alpha D.transporter =
    (alpha D.transporter : R) • (1 : Module.End R V) := by
  change (alpha D.transporter : R) • T (D.transporter : G) = _
  rw [D.tate_transporter]

theorem twist_transporter_inv : twist H T alpha D.transporter⁻¹ =
    (D.transportUnit : R) • (1 : Module.End R V) := by
  have ht : T ((D.transporter⁻¹ : H) : G) = 1 := by
    have h := T.map_mul (D.transporter : G) (D.transporter : G)⁻¹
    simpa [D.tate_transporter] using h.symm
  change (alpha D.transporter⁻¹ : R) • T ((D.transporter⁻¹ : H) : G) = _
  rw [ht, map_inv]
  rfl

theorem tate_finite : T (D.finiteGenerator : G) = 1 := by
  rw [D.finite_eq, map_pow, D.tate_frobenius, ← map_pow, D.tau_sq, map_one]

theorem twist_finite : twist H T alpha D.finiteGenerator = 1 := by
  simp [twist, D.alpha_finite, D.tate_finite]

theorem twist_inertia : twist H T alpha D.inertia = 1 := by
  simp [twist, D.alpha_inertia, D.tate_inertia]

variable [H.Normal]

/-- Raw pullback, with conjugate coefficients. -/
def rawConjugate (p : H → V) : H → V := p ∘ conjugation H D.tau

theorem rawConjugate_isCrossed (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    IsCrossed ((twist H T alpha).comp (conjugation H D.tau)) (D.rawConjugate p) := by
  intro g h
  simpa [rawConjugate] using hp (conjugation H D.tau g) (conjugation H D.tau h)

theorem conjugation_finite : conjugation H D.tau D.finiteGenerator =
    D.transporter⁻¹ * D.finiteGenerator * D.transporter := by
  apply Subtype.ext
  change D.tau * (D.finiteGenerator : G) * D.tau⁻¹ =
    (D.transporter : G)⁻¹ * (D.finiteGenerator : G) * (D.transporter : G)
  have ht : D.tau = (D.transporter : G)⁻¹ * D.frobenius := by
    rw [D.frobenius_eq]; group
  rw [ht, D.finite_eq]
  group

theorem conjugation_inertia : conjugation H D.tau D.inertia =
    D.transporter⁻¹ * D.inertia ^ D.ell * D.transporter := by
  apply Subtype.ext
  change D.tau * (D.inertia : G) * D.tau⁻¹ =
    (D.transporter : G)⁻¹ * (D.inertia : G) ^ D.ell * (D.transporter : G)
  have ht : D.tau = (D.transporter : G)⁻¹ * D.frobenius := by
    rw [D.frobenius_eq]; group
  rw [ht]
  calc
    _ = (D.transporter : G)⁻¹ *
        (D.frobenius * (D.inertia : G) * D.frobenius⁻¹) * (D.transporter : G) := by group
    _ = _ := by rw [D.tame_eq]

theorem rawConjugate_finite (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.rawConjugate p D.finiteGenerator = (D.transportUnit : R) • p D.finiteGenerator := by
  change p (conjugation H D.tau D.finiteGenerator) = _
  rw [D.conjugation_finite, crossed_conjugation _ p hp,
    D.twist_finite, Module.End.one_apply, add_sub_cancel_right, D.twist_transporter_inv]
  rfl

theorem rawConjugate_inertia (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.rawConjugate p D.inertia =
      (D.transportUnit : R) • ((D.ell : R) • p D.inertia) := by
  change p (conjugation H D.tau D.inertia) = _
  rw [D.conjugation_inertia, crossed_conjugation _ p hp,
    map_pow, D.twist_inertia, one_pow, Module.End.one_apply,
    add_sub_cancel_right, D.twist_transporter_inv]
  change (D.transportUnit : R) • p (D.inertia ^ D.ell) = _
  rw [crossed_pow_of_trivial _ p hp D.inertia D.twist_inertia]

/-- Integral transport, before reducing the tame factor to minus one. -/
theorem coordinates_rawConjugate (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.coordinates (D.rawConjugate p) =
      ((D.transportUnit : R) • (D.coordinates p).1,
       (D.transportUnit : R) • ((D.ell : R) • (D.coordinates p).2)) := by
  exact Prod.ext (D.rawConjugate_finite p hp) (D.rawConjugate_inertia p hp)

/-- The local-conjugation input of the arithmetic bridge is derived from H12
and the twisted representation, with one actual unit for every class. -/
theorem coordinates_rawConjugate_of_neg_one (hEll : (D.ell : R) = -1)
    (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.coordinates (D.rawConjugate p) =
      ((D.transportUnit : R) • (D.coordinates p).1,
       -((D.transportUnit : R) • (D.coordinates p).2)) := by
  rw [D.coordinates_rawConjugate p hp, hEll, neg_one_smul, smul_neg]

theorem twist_conjugation_finite :
    twist H T alpha (conjugation H D.tau D.finiteGenerator) = 1 := by
  rw [D.conjugation_finite, map_mul, map_mul, D.twist_finite, mul_one,
    ← map_mul, inv_mul_cancel, map_one]

theorem twist_conjugation_inertia :
    twist H T alpha (conjugation H D.tau D.inertia) = 1 := by
  rw [D.conjugation_inertia, map_mul, map_mul, map_pow, D.twist_inertia,
    one_pow, mul_one, ← map_mul, inv_mul_cancel, map_one]

omit [H.Normal] in
/-- Changing representatives by a coboundary does not change local coordinates. -/
theorem coordinates_add_coboundary (p : H → V) (v : V) :
    D.coordinates (fun h => p h + (twist H T alpha h v - v)) = D.coordinates p := by
  simp [coordinates, D.twist_finite, D.twist_inertia]

/-- The same assertion for the conjugate coefficient system, not an assertion
that the raw conjugate is a cocycle for the original representation. -/
theorem conjugate_coordinates_add_coboundary (p : H → V) (v : V) :
    D.coordinates (D.rawConjugate (fun h => p h + (twist H T alpha h v - v))) =
      D.coordinates (D.rawConjugate p) := by
  simp [coordinates, rawConjugate, D.twist_conjugation_finite, D.twist_conjugation_inertia]

end LocalData

end Research.DerivativeSwitch.ConjugateLocalTransport
