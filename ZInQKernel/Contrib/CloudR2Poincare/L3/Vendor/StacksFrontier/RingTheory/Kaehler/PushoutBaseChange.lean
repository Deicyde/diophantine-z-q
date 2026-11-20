import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.RingTheory.Kaehler.PushoutBaseChange`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Differentials of a formally étale extension of a pushout

Let `R → A` and `R → B` be ring maps, let `T` be their pushout `A ⊗[R] B`, and let `T → C` be
formally étale. Then

```
C ⊗[A] Ω[A⁄R] ≃ Ω[C⁄B],
```

the universal differential `1 ⊗ d a` corresponding to `d (image of a)`. The two ingredients are
the base change formula for Kähler differentials along the pushout square and the invariance of
differentials under a formally étale extension; both are in Mathlib as base change statements,
and composing them is what produces the displayed identification.

## Main definitions

* `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout` is the identification above.

## Main results

* `KaehlerDifferential.isBaseChange_map_of_isPushout`: for a pushout square, `Ω[T⁄B]` is the base
  change of `Ω[A⁄R]` along `A → T`. This is the `IsBaseChange` form of Mathlib's
  `KaehlerDifferential.tensorKaehlerEquiv`, which is Stacks Project, Tag 00RV.
* `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout_tmul_D`: the identification
  carries universal differentials to universal differentials.

## Implementation notes

The hypotheses are the ones the two Mathlib statements need and no more: `C` is not assumed to be
a localization of `T`, only formally étale over it, which is what the proof of the base change
formula for differentials of a fibre product of schemes supplies at a point.

## References

* [Stacks Project, Tag 00RV](https://stacks.math.columbia.edu/tag/00RV)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
-/


open scoped TensorProduct

namespace KaehlerDifferential
#cloudR2LocalInstances

variable (R A B T C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing T] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
  [IsScalarTower R A T] [IsScalarTower R B T]
#cloudR2Vendor isBaseChange_map_of_isPushout in

/-- **For a pushout square `T = A ⊗[R] B`, the module `Ω[T⁄B]` is the base change of `Ω[A⁄R]`
along `A → T`.** This is Mathlib's `KaehlerDifferential.tensorKaehlerEquiv`, which is the
sheafifiable content of Stacks Project, Tag 00RV, read as a base change statement so that it
composes with other base changes. -/
theorem isBaseChange_map_of_isPushout [Algebra.IsPushout R B A T] :
    IsBaseChange T (KaehlerDifferential.map R B A T) := by
  refine IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R B A T) ?_
  have he : (KaehlerDifferential.tensorKaehlerEquiv R B A T).toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.mk A T Ω[A⁄R] 1 = KaehlerDifferential.map R B A T := by
    refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A) ?_
    intro a
    simp
  exact DFunLike.congr_fun he

variable [Algebra A C] [Algebra B C] [Algebra T C] [IsScalarTower A T C] [IsScalarTower B T C]
#cloudR2Vendor tensorKaehlerEquivOfFormallyEtalePushout in

/-- **The differentials of a formally étale extension of a pushout.** For a pushout square
`T = A ⊗[R] B` and a formally étale `T`-algebra `C`, the `C`-module `Ω[C⁄B]` is the base change
of `Ω[A⁄R]` along `A → C`. -/

noncomputable def tensorKaehlerEquivOfFormallyEtalePushout [Algebra.IsPushout R B A T]
    [Algebra.FormallyEtale T C] :
    C ⊗[A] Ω[A⁄R] ≃ₗ[C] Ω[C⁄B] :=
  ((isBaseChange_map_of_isPushout R A B T).comp
    (KaehlerDifferential.isBaseChange_of_formallyEtale B T C)).equiv
#cloudR2Vendor tensorKaehlerEquivOfFormallyEtalePushout_tmul_D in

/-- **The identification of `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout`
carries universal differentials to universal differentials**: `1 ⊗ d a` goes to `d` of the image
of `a` in `C`. -/
theorem tensorKaehlerEquivOfFormallyEtalePushout_tmul_D [Algebra.IsPushout R B A T]
    [Algebra.FormallyEtale T C] (a : A) :
    tensorKaehlerEquivOfFormallyEtalePushout R A B T C
        ((1 : C) ⊗ₜ[A] KaehlerDifferential.D R A a) =
      KaehlerDifferential.D B C (algebraMap A C a) := by
  simp only [tensorKaehlerEquivOfFormallyEtalePushout, IsBaseChange.equiv_tmul, one_smul,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, KaehlerDifferential.map_D]
  rw [← IsScalarTower.algebraMap_apply A T C]

end KaehlerDifferential


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
