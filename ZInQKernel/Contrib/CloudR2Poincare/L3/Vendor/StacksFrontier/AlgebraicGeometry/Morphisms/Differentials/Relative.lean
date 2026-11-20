import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.Topology.Sheaves.Modules.Differentials
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# The sheaf of relative differentials of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, the sheaf of relative differentials is the module
representing derivations of the structure sheaf of `X` relative to the inverse image of the
structure sheaf of `S`, together with its universal derivation.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` is the sheaf of relative differentials
  of a morphism of schemes.
* `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation` is its universal relative
  derivation.

## Implementation notes

The structural map of a morphism of schemes is `AlgebraicGeometry.inverseImageStructureMap`,
and the representing module and its universal derivation are the sheaf-theoretic
constructions for that map. So these are definitions rather than constructions: all the
content is in the representability of the derivations functor.

## References

* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
-/


open _root_.CategoryTheory _root_.TopologicalSpace
open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom
#cloudR2LocalInstances

/-- The sheaf of relative differentials of a morphism of schemes, formed over the inverse
image of the structure sheaf of the base. -/
noncomputable def relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules :=
  SheafOfModules.moduleOfDifferentials (inverseImageStructureMap f)
#cloudR2Vendor universalRelativeDerivation in

/-- The universal relative derivation of the structure sheaf of the source of a morphism of
schemes into its sheaf of relative differentials. -/

noncomputable def universalRelativeDerivation {X S : Scheme.{u}} (f : X ⟶ S) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap f) (_root_.ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f) :=
  SheafOfModules.universalDerivation (inverseImageStructureMap f)
#cloudR2Vendor app_eq_inverseImageStructureMap in

/-- **The comorphism of `f` factors through the structural map `f⁻¹𝒪_S ⟶ 𝒪_X`.** On sections
over an open `W` of `S`, `f^♯` is the unit of `f⁻¹ ⊣ f_*` at `𝒪_S` followed by
`AlgebraicGeometry.inverseImageStructureMap`.

This is the definition of `AlgebraicGeometry.inverseImageStructureMap` as the adjunct of `f.c`,
read on sections. -/
theorem app_eq_inverseImageStructureMap {X S : Scheme.{u}} (f : X ⟶ S) (W : S.Opens)
    (r : Γ(S, W)) :
    (f.app W).hom r =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app S.sheaf ≫
          (TopCat.Sheaf.pushforward CommRingCat f.base).map
            (inverseImageStructureMap f)).hom.app (Opposite.op W)).hom r := by
  have h2 := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv
    S.sheaf X.sheaf).apply_symm_apply (⟨f.c⟩ :
      S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)
  rw [Adjunction.homEquiv_unit] at h2
  exact (congrArg (fun ψ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf ↦
    (ψ.hom.app (Opposite.op W)).hom r) h2).symm
#cloudR2Vendor universalRelativeDerivation_d_app_eq_zero in

/-- **The universal relative derivation kills the sections coming from the base.** For a section
`r` of `𝒪_S` over an open `W` of `S`, `d_{X/S} (f^♯ r) = 0`.

The vanishing of a relative derivation on the image of the structural map `f⁻¹𝒪_S ⟶ 𝒪_X` is one
of the defining conditions of `AlgebraicGeometry.SheafOfModules.SheafDerivation`; this is that
condition read through `AlgebraicGeometry.Scheme.Hom.app_eq_inverseImageStructureMap`. -/
theorem universalRelativeDerivation_d_app_eq_zero {X S : Scheme.{u}} (f : X ⟶ S) (W : S.Opens)
    (r : Γ(S, W)) : (universalRelativeDerivation f).d ((f.app W).hom r) = 0 :=
  (congrArg (fun y : Γ(X, f ⁻¹ᵁ W) ↦ (universalRelativeDerivation f).d y)
    (app_eq_inverseImageStructureMap f W r)).trans
      ((universalRelativeDerivation f).d_app
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
          S.sheaf).hom.app (Opposite.op W)).hom r))

end AlgebraicGeometry.Scheme.Hom

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
