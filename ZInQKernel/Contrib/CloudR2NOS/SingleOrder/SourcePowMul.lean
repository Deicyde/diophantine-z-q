/-
# H5 / NOS round 2, lane 1: double Source tensor powers `(Lᵃ)ᵇ ≅ L^{a·b}`

Newly authored glue (H5 round-2 lane 1, 2026-11-15). Uses ONLY the canonical Source port's literal
`Scheme.Modules.tensorPow` (recursive `𝟙_` / `_ ⊗ L`, Source monoidal structure) and its `tensorPowAdd`
(FLT @ 6e837e75…, Apache-2.0, Anthropic, PBC). This file deliberately imports no W07 module, so every
monoidal notation below is the Source's own structure (no other monoidal instance is in scope).
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.SourcePowMul

variable {X : Scheme.{u}}

/-- `(L^{⊗a})^{⊗b} ≅ L^{⊗(a·b)}` for the literal Source tensor powers, by induction on `b` with the Source
associator-based `tensorPowAdd`. -/
def tensorPowMul (L : X.Modules) (a : ℕ) : (b : ℕ) →
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow L a) b ≅
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow L (a * b))
  | 0 => Iso.refl _
  | b + 1 => whiskerRightIso (tensorPowMul L a b)
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow L a) ≪≫
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowAdd L (a * b) a

/-- The double-power comparison exists, and the combined exponent is positive when both are. -/
theorem nonempty_tensorPowMul (L : X.Modules) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    0 < a * b ∧ Nonempty
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow
          (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow L a) b ≅
        ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow L (a * b)) :=
  ⟨Nat.mul_pos ha hb, ⟨tensorPowMul L a b⟩⟩

end ZInQ.Contrib.CloudR2NOS.SingleOrder.SourcePowMul
