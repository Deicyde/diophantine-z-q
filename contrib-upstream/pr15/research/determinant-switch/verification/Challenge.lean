import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Ring

/-!
Frozen specification for the six abstract research lemmas in CONTRACT.md.
This file deliberately does not import the solution. Its six `sorry` bodies
are specification placeholders, never accepted proofs. It is excluded from
the default solution target. The comparator permits no definition holes:
AxesKernel, area, and action must retain the definitions below.
-/

namespace Research.DerivativeSwitch

variable {K F S H : Type*}
variable [Field K]
variable [AddCommGroup F] [Module K F]
variable [AddCommGroup S] [Module K S]
variable [AddCommGroup H] [Module K H]

def AxesKernel
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (J : F ≃ₗ[K] S) (v : F) : Prop :=
  ∀ x : F, ∀ y : S,
    dF x + dS y = 0 ↔
      ∃ a b : K, x = a • v ∧ y = b • (J v)

theorem finite_kernel_line
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (J : F ≃ₗ[K] S) (v : F)
    (hker : AxesKernel dF dS J v) (x : F) :
    dF x = 0 ↔ ∃ a : K, x = a • v := by sorry

theorem singular_kernel_line
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (J : F ≃ₗ[K] S) (v : F)
    (hker : AxesKernel dF dS J v) (y : S) :
    dS y = 0 ↔ ∃ b : K, y = b • (J v) := by sorry

theorem boundary_images_meet_zero
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (J : F ≃ₗ[K] S) (v : F)
    (hker : AxesKernel dF dS J v)
    (x : F) (y : S) (heq : dF x = dS y) :
    dF x = 0 ∧ dS y = 0 := by sorry

theorem no_identity_strict_square
    (dF : F →ₗ[K] H) (dS : S →ₗ[K] H)
    (J : F ≃ₗ[K] S) (v : F)
    (hker : AxesKernel dF dS J v)
    (hout : ∃ x : F, ∀ a : K, x ≠ a • v) :
    ¬ ∀ x : F, dF x = dS (J x) := by sorry

end Research.DerivativeSwitch

namespace Research.DerivativeSwitch.Volume

variable {R : Type*} [CommRing R]

def area (v w : R × R) : R := v.1 * w.2 - v.2 * w.1

def action (a b c d : R) (v : R × R) : R × R :=
  (a * v.1 + b * v.2, c * v.1 + d * v.2)

theorem area_action (a b c d : R) (v w : R × R) :
    area (action a b c d v) (action a b c d w) =
      (a * d - b * c) * area v w := by sorry

theorem area_neg_one
    (a b c d : R) (v w : R × R)
    (hdet : a * d - b * c = -1)
    (hvol : area v w = 1) :
    area (action a b c d v) (action a b c d w) = -1 := by sorry

end Research.DerivativeSwitch.Volume
