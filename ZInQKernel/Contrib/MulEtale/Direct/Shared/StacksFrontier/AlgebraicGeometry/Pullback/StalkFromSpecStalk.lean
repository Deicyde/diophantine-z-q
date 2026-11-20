module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Localization
public import ZInQKernel.Contrib.CloudW01Spread.StacksCore.Tactic.EgaSgaAttribute
public import ZInQKernel.Contrib.CloudW01Spread.StacksCore.Tactic.StacksAttribute

-- Exact source: https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/Pullback/StalkFromSpecStalk.lean
-- Original source SHA256: 7926e7b5ab61868e698958462c20045c7b7f862aecd754fca9ae5c33e070fbf5
-- Apache 2.0; original notices retained; see the owned LICENSE and NOTICE.md.
-- Isolated proof declarations; citation metadata is shared with the tangent modules.
namespace ZInQ.Contrib.MulEtale.StacksVendor
open _root_.AlgebraicGeometry _root_.CategoryTheory
set_option autoImplicit false



/-!
# Base change along the canonical morphism out of the spectrum of a local ring

For a scheme `X` and a point `x` of `X` the canonical morphism `X.fromSpecStalk x`,
`Spec 𝒪_{X, x} ⟶ X`, is **flat** and a **preimmersion**: on an affine open neighbourhood `U` of
`x` it is `Spec` of the germ map `Γ(X, U) → 𝒪_{X, x}`, which exhibits `𝒪_{X, x}` as a
localization of `Γ(X, U)`. Both properties are stable under base change, and a flat preimmersion
induces isomorphisms on local rings, because such a map on local rings is surjective by the
preimmersion hypothesis and injective because a flat local homomorphism is faithfully flat.

Consequently, for any morphism `ν : Y ⟶ X` the first projection of `Y ×_X Spec 𝒪_{X, x}` is an
isomorphism on every local ring, and its image is the set of points of `Y` specializing into
`x`. In particular every point `y` of `Y` lying over `x` is hit, so the fibre product has a
point over `y` whose local ring is `𝒪_{Y, y}`.

## Main results

* `AlgebraicGeometry.flat_fromSpecStalk`: the canonical morphism `Spec 𝒪_{X, x} ⟶ X` is flat.
* `AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`: a flat preimmersion induces
  isomorphisms on local rings.
* `AlgebraicGeometry.exists_point_pullback_fromSpecStalk_isIso_stalkMap`: for `ν : Y ⟶ X` and a
  point `y` of `Y` above `x`, the fibre product `Y ×_X Spec 𝒪_{X, x}` has a point over `y` at
  which the first projection induces an isomorphism of local rings.

## References

* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7), which computes the
  image of `Spec 𝒪_{X, x} ⟶ X`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The canonical morphism `Spec 𝒪_{X,x} ⟶ X` is flat.** On an affine open neighbourhood `U`
of `x` it is `Spec` of the germ map `Γ(X, U) → 𝒪_{X, x}`, which exhibits `𝒪_{X, x}` as a
localization of `Γ(X, U)` and is therefore flat. -/
public lemma flat_fromSpecStalk (X : Scheme.{u}) (x : X) :
    Flat (X.fromSpecStalk x) := by
  let U := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := X.affineCover.covers x
  change Flat (hU.fromSpecStalk hx)
  dsimp [IsAffineOpen.fromSpecStalk]
  have hflat : (X.presheaf.germ U x hx).hom.Flat := by
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := Flat.SpecMap_iff.mpr hflat
  infer_instance

/-- **A flat preimmersion induces isomorphisms on local rings.** Surjectivity of the map on
local rings is part of being a preimmersion, and injectivity holds because a flat local
homomorphism is faithfully flat, hence injective. -/
public lemma isIso_stalkMap_of_flat_isPreimmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [Flat g] [IsPreimmersion g] (x : X) : IsIso (g.stalkMap x) := by
  have hinj : Function.Injective (g.stalkMap x).hom := by
    algebraize [(g.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap g x) (g.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, g.stalkMap_surjective x⟩
end AlgebraicGeometry

end
