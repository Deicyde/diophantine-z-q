/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicCurve_RiemannRochRows. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def RiemannInequality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F, Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ)

def RiemannIndexFormula : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F,
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))

def WeilDualityAdelic : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (indexOfSpecialty D : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

def WeilDuality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))
        = (ell (canonicalDivisorOf hω - D) : ℤ)

def WeilOmegaEllAgrees : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (Module.finrank K ↥(omegaSpace D) : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

def FunctionFieldRiemannRoch : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (ell (canonicalDivisorOf hω - D) : ℤ)
        = Divisor.degree D + 1 - (genus K F : ℤ)

theorem functionFieldRiemannRoch_of_riemann_and_duality
    (hWD : WeilDuality K F) : FunctionFieldRiemannRoch K F := by
  intro _ _ _ ω hω D
  linarith [hWD hω D]

theorem weilDuality_of_riemannIndex_of_adelic
    (hRI : RiemannIndexFormula K F) (hWD : WeilDualityAdelic K F) :
    WeilDuality K F := by
  intro _ _ _ ω hω D
  have h1 := hRI D
  have h2 := hWD hω D
  linarith

end AlgebraicCurve

end
