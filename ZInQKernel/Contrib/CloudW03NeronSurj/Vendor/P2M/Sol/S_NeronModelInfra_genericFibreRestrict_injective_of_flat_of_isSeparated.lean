/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 2 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 3 `p2m_*` command(s) renamed to `w03_*`.
  * 1 scope(s) the source leaves open at EOF closed explicitly (end P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
    (Correction, 2026-11-14: a surplus `end NeronModelInfra` was removed here; the source's dotted
    `end NeronModelInfra.GenericFibreRestrictInjective` already closes both of those scopes.)
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.NeronModelInfra"

namespace NeronModelInfra
w03_export "NeronModelInfra" "specGenericFibreInclusion SchemeHomOver genericFibreRestrict genericFibreRestrict_coe_comp_fst"
namespace GenericFibreRestrictInjective
w03_open "NeronModelInfra"

theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W T X S : Scheme.{u}}
    {a b : T ⟶ X} (f : X ⟶ S) [IsSeparated f] (t : T ⟶ S) (ha : a ≫ f = t) (hb : b ≫ f = t)
    (p : W ⟶ T) [IsSchemeTheoreticallyDominant p] (h : p ≫ a = p ≫ b) : a = b := by
  let X' : Over S := Over.mk f
  let T' : Over S := Over.mk t
  let a' : T' ⟶ X' := Over.homMk a ha
  let b' : T' ⟶ X' := Over.homMk b hb
  let p' : Over.mk (p ≫ t) ⟶ T' := Over.homMk p rfl
  have hp' : p' ≫ a' = p' ≫ b' := Over.OverMorphism.ext (by simpa [a', b', p'] using h)
  let l : Over.mk (p ≫ t) ⟶ equalizer a' b' := equalizer.lift p' hp'
  have hl : l ≫ equalizer.ι a' b' = p' := equalizer.lift_ι _ _
  haveI : IsSeparated X'.hom := ‹IsSeparated f›
  haveI : IsClosedImmersion (equalizer.ι a' b').left := isClosedImmersion_equalizer_ι_left a' b'
  have hcomp : l.left ≫ (equalizer.ι a' b').left = p := by
    rw [← Over.comp_left, hl]; rfl
  have hker : Scheme.Hom.ker (equalizer.ι a' b').left = ⊥ := by
    have h1 := Scheme.Hom.le_ker_comp l.left (equalizer.ι a' b').left
    rw [hcomp] at h1
    exact le_bot_iff.mp (h1.trans (le_of_eq (Scheme.Hom.ker_eq_bot p)))
  have hiso : IsIso (equalizer.ι a' b').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hcond : (equalizer.ι a' b').left ≫ a = (equalizer.ι a' b').left ≫ b := by
    have := equalizer.condition a' b'
    simpa [a', b'] using congrArg CommaMorphism.left this
  haveI : Epi (equalizer.ι a' b').left := @IsIso.epi_of_iso _ _ _ _ _ hiso
  exact (cancel_epi (equalizer.ι a' b').left).mp hcond

end NeronModelInfra.GenericFibreRestrictInjective

open NeronModelInfra.GenericFibreRestrictInjective in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [Flat t] :
    Function.Injective (genericFibreRestrict R K f t) := by
  intro φ ψ h
  have h1 : pullback.fst t (specGenericFibreInclusion R K) ≫ φ.1 =
      pullback.fst t (specGenericFibreInclusion R K) ≫ ψ.1 := by
    have := congrArg (fun χ : SchemeHomOver _ _ => χ.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) h
    rwa [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst] at this
  haveI : IsDominant (specGenericFibreInclusion R K) := by
    rw [isDominant_iff, specGenericFibreInclusion]
    have : RingHom.ker (algebraMap R K) ≤ nilradical R := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
      exact bot_le
    have h__af := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr this
    simp at h__af ⊢
    exact h__af
  haveI : IsSchemeTheoreticallyDominant (specGenericFibreInclusion R K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  haveI : IsSchemeTheoreticallyDominant (pullback.fst t (specGenericFibreInclusion R K)) :=
    IsSchemeTheoreticallyDominant.pullbackFst t _
  exact Subtype.ext (ext_of_isSchemeTheoreticallyDominant_of_isSeparated f t φ.2 ψ.2 _ h1)

end P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated

end ZInQ.Contrib.CloudW03NeronSurj.FLT
