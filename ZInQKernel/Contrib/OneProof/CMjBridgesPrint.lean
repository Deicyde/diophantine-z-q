import ZInQKernel.Contrib.OneProof.FowlerBridges
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_ofTau
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

namespace HDec.CMBranch.CMjBridges

open scoped UpperHalfPlane
open NumberField TauCeti.GlobalNumberFields

/-- The classical modular j, normalized to take the value 1728 at i, via the lattice
with generators 1 and τ. -/
noncomputable def modularJ (τ : ℍ) : ℂ := (PeriodPair.ofTau τ).jLattice

/-- The lattice definition agrees with the usual normalized modular form formula. -/
theorem modularJ_eq (τ : ℍ) :
    modularJ τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ :=
  PeriodPair.jLattice_ofTau τ

/-- Fowler p. 612: the discriminant of a quadratic upper half-plane period is
`b² − 4ac` for its primitive equation `aτ² + bτ + c = 0`. We choose the sign
so that `a > 0`; a nonreal root cannot have a nonzero linear equation over ℚ. -/
def PeriodDiscriminant (τ : ℍ) (Δ : ℤ) : Prop :=
  ∃ a b c : ℤ, 0 < a ∧ Int.gcd (Int.gcd a b) c = 1 ∧
    (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0 ∧ b ^ 2 - 4 * a * c = Δ

/-- A singular modulus of discriminant Δ, in the analytic terms of Fowler p. 612. -/
def IsSingularModulusOfDisc (x : ℂ) (Δ : ℤ) : Prop :=
  ∃ τ : ℍ, x = modularJ τ ∧ PeriodDiscriminant τ Δ

/-- Fowler, *Some uniform effective results on André–Oort for sums of powers in ℂⁿ*,
Math. Proc. Cambridge Philos. Soc. 180 (2026), §2·1, p. 613:
“[ℚ(xᵢ) : ℚ] = [ℚ(√Δ, xᵢ) : ℚ(√Δ)] = h(Δ), where h(Δ) denotes the class number
of the imaginary quadratic order of discriminant Δ.”

We use the equality over ℚ. The input is a singular modulus `x = j(τ)` for a
quadratic upper half-plane period, with its primitive equation as on p. 612.
Page 607 describes the same discriminant via the endomorphism order. As in
`FowlerBridges.FowlerProp27Print`, the order of discriminant Δ is an explicit
parameter, with class number counting its proper fractional ideal classes.
Human reading of the publisher PDF: fork issue #14, comment 6973419601. -/
def CMjDegreePrint : Prop :=
  ∀ (x : ℂ) (Δ : ℤ), IsSingularModulusOfDisc x Δ →
    ∀ (k : Type) [Field k] [NumberField k] [IsTotallyComplex k],
      Module.finrank ℚ k = 2 → ∀ (O : NumberFieldOrder k), O.discr = Δ →
        Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = FowlerBridges.properClassNumber O

end HDec.CMBranch.CMjBridges
