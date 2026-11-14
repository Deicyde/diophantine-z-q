import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.Descent.B2Assembly

/-!
Independent full target for coefficient transport of a GIVEN B2 cochain.
No assertion that the B2 literature inputs, arithmetic field or global C10 bundle are constructed.
-/

noncomputable section
namespace ClimbBetaExpected

/-- The fixed complex place acts on units; no second place is chosen. -/
def unitPlace (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) : GlueC10.Qbarˣ →* ℂˣ :=
  Units.map ρ.toRingHom.toMonoidHom

/-- The same original cyclotomic map, with the given Qbar-valued character. -/
def galCharacter {N : ℕ} [NeZero N] (χ₀ : DirichletCharacter GlueC10.Qbar N) :
    GlueDescent.B2Q.GQ →* GlueC10.Qbarˣ :=
  χ₀.toUnitHom.comp (GlueDescent.B2Q.cyc N)

/-- Lift literal supplied beta values and their square/cochain equations through the fixed place. -/
def GivenB2CoefficientTransport : Prop :=
  ∀ (N : ℕ) [NeZero N] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (χ₀ : DirichletCharacter GlueC10.Qbar N) (χ : DirichletCharacter ℂ N),
    (∀ a : ZMod N, ρ (χ₀ a) = χ a) →
    ∀ (β : GlueDescent.B2Q.GQ → ℂˣ), IsLocallyConstant β →
      (∀ g, β g ^ 2 = GlueDescent.B2Q.galChar χ g) →
      ∀ (ε₀ : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → GlueC10.Qbarˣ),
        (∀ g h, β g * β h = unitPlace ρ (ε₀ g h) * β (g * h)) →
        ∃ β₀ : GlueDescent.B2Q.GQ → GlueC10.Qbarˣ,
          (∀ g, unitPlace ρ (β₀ g) = β g) ∧ IsLocallyConstant β₀ ∧
          (∀ g, β₀ g ^ 2 = galCharacter χ₀ g) ∧
          (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) ∧
          (∀ g, (β₀ g : GlueC10.Qbar) ≠ 0)

/-- Normalization is a separate source condition, not implied by the unnormalized sign-cocycle def. -/
def NormalizationFromUnitEquation : Prop :=
  ∀ (ε₀ : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → GlueC10.Qbarˣ)
    (β₀ : GlueDescent.B2Q.GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) →
      ε₀ 1 1 = 1 → β₀ 1 = 1

end ClimbBetaExpected
