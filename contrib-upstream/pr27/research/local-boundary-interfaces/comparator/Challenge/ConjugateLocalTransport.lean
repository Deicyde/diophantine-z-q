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
  sorry

theorem crossed_pow_of_trivial (rho : G →* Module.End R V) (p : G → V)
    (hp : IsCrossed rho p) (x : G) (hx : rho x = 1) (n : ℕ) :
    p (x ^ n) = (n : R) • p x := by
  sorry

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
  sorry

theorem twist_transporter : twist H T alpha D.transporter =
    (alpha D.transporter : R) • (1 : Module.End R V) := by
  sorry

theorem twist_transporter_inv : twist H T alpha D.transporter⁻¹ =
    (D.transportUnit : R) • (1 : Module.End R V) := by
  sorry

theorem tate_finite : T (D.finiteGenerator : G) = 1 := by
  sorry

theorem twist_finite : twist H T alpha D.finiteGenerator = 1 := by
  sorry

theorem twist_inertia : twist H T alpha D.inertia = 1 := by
  sorry

variable [H.Normal]

/-- Raw pullback, with conjugate coefficients. -/
def rawConjugate (p : H → V) : H → V := p ∘ conjugation H D.tau

theorem rawConjugate_isCrossed (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    IsCrossed ((twist H T alpha).comp (conjugation H D.tau)) (D.rawConjugate p) := by
  sorry

theorem conjugation_finite : conjugation H D.tau D.finiteGenerator =
    D.transporter⁻¹ * D.finiteGenerator * D.transporter := by
  sorry

theorem conjugation_inertia : conjugation H D.tau D.inertia =
    D.transporter⁻¹ * D.inertia ^ D.ell * D.transporter := by
  sorry

theorem rawConjugate_finite (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.rawConjugate p D.finiteGenerator = (D.transportUnit : R) • p D.finiteGenerator := by
  sorry

theorem rawConjugate_inertia (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.rawConjugate p D.inertia =
      (D.transportUnit : R) • ((D.ell : R) • p D.inertia) := by
  sorry

/-- Integral transport, before reducing the tame factor to minus one. -/
theorem coordinates_rawConjugate (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.coordinates (D.rawConjugate p) =
      ((D.transportUnit : R) • (D.coordinates p).1,
       (D.transportUnit : R) • ((D.ell : R) • (D.coordinates p).2)) := by
  sorry

/-- The local-conjugation input of the arithmetic bridge is derived from H12
and the twisted representation, with one actual unit for every class. -/
theorem coordinates_rawConjugate_of_neg_one (hEll : (D.ell : R) = -1)
    (p : H → V) (hp : IsCrossed (twist H T alpha) p) :
    D.coordinates (D.rawConjugate p) =
      ((D.transportUnit : R) • (D.coordinates p).1,
       -((D.transportUnit : R) • (D.coordinates p).2)) := by
  sorry

theorem twist_conjugation_finite :
    twist H T alpha (conjugation H D.tau D.finiteGenerator) = 1 := by
  sorry

theorem twist_conjugation_inertia :
    twist H T alpha (conjugation H D.tau D.inertia) = 1 := by
  sorry

omit [H.Normal] in
/-- Changing representatives by a coboundary does not change local coordinates. -/
theorem coordinates_add_coboundary (p : H → V) (v : V) :
    D.coordinates (fun h => p h + (twist H T alpha h v - v)) = D.coordinates p := by
  sorry

/-- The same assertion for the conjugate coefficient system, not an assertion
that the raw conjugate is a cocycle for the original representation. -/
theorem conjugate_coordinates_add_coboundary (p : H → V) (v : V) :
    D.coordinates (D.rawConjugate (fun h => p h + (twist H T alpha h v - v))) =
      D.coordinates (D.rawConjugate p) := by
  sorry

end LocalData

end Research.DerivativeSwitch.ConjugateLocalTransport
