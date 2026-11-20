import ZInQKernel.Contrib.CloudR2CM.SerreTate.P4.ValuativeBaseFactor
import ZInQKernel.Contrib.OneProof.H.TailZ19
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Localization.Defs

/-!
# Properness from maximal localizations over a ring of integers

Valuative test maps factor through the generic field when their center is
zero and through the actual center localization otherwise. The target of
localization lifting remains the original arbitrary valuation ring.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField

namespace HDec.CMSerreTate.P4

/-- Properness of the generic fibre and every maximal localization gives
properness over the ring of integers, by the full valuative criterion. -/
theorem isProper_of_generic_and_maximal_localizations (F : Type) [Field F] [NumberField F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (𝓞 F)))
    [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    (hGeneric : IsProper (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F)))))
    (hLocal : ∀ (𝔭 : Ideal (𝓞 F)) [𝔭.IsMaximal],
      IsProper (pullback.snd f (_root_.ReductGlue.gO (_root_.ReductGlue.dvrAt 𝔭)))) :
    IsProper f := by
  classical
  apply isProper_of_proper_base_factor f
  intro S
  let α : 𝓞 F →+* S.R := (Spec.preimage S.i₂).hom
  let 𝔭 : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal S.R).comap α
  have hα : Spec.map (CommRingCat.ofHom α) = S.i₂ := by
    simpa only [α, CommRingCat.ofHom_hom] using Spec.map_preimage S.i₂
  by_cases h𝔭 : 𝔭 = ⊥
  · have hUnits : ∀ s : nonZeroDivisors (𝓞 F), IsUnit (α s) := by
      intro s
      by_contra hs
      have hm : α (s : 𝓞 F) ∈ IsLocalRing.maximalIdeal S.R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hs
      have hp : (s : 𝓞 F) ∈ 𝔭 := hm
      rw [h𝔭, Ideal.mem_bot] at hp
      exact nonZeroDivisors.ne_zero s.2 hp
    let β : F →+* S.R := IsLocalization.lift (S := F) hUnits
    have hβ : β.comp (algebraMap (𝓞 F) F) = α := IsLocalization.lift_comp hUnits
    refine ⟨Spec (CommRingCat.of F),
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F)),
      Spec.map (CommRingCat.ofHom β), ?_, hGeneric⟩
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hβ]
    exact hα
  · have hPrime : 𝔭.IsPrime := Ideal.comap_isPrime _ _
    letI : 𝔭.IsPrime := hPrime
    letI : 𝔭.IsMaximal := hPrime.isMaximal h𝔭
    let O : ValuationSubring F := _root_.ReductGlue.dvrAt 𝔭
    letI : Algebra (𝓞 F) O := _root_.CToPrinted.algOL O
    haveI : IsLocalization.AtPrime O 𝔭 := by
      simpa only [O, _root_.ReductGlue.center_dvrAt] using
        (_root_.CToPrinted.isLocalization_center O)
    have hUnits : ∀ s : 𝔭.primeCompl, IsUnit (α s) := by
      intro s
      by_contra hs
      have hp : (s : 𝓞 F) ∈ 𝔭 := (IsLocalRing.mem_maximalIdeal _).mpr hs
      exact s.2 hp
    let β : O →+* S.R := IsLocalization.lift (S := O) hUnits
    have hβ : β.comp (algebraMap (𝓞 F) O) = α := IsLocalization.lift_comp hUnits
    refine ⟨Spec (CommRingCat.of O), _root_.ReductGlue.gO O,
      Spec.map (CommRingCat.ofHom β), ?_, hLocal 𝔭⟩
    change Spec.map (CommRingCat.ofHom β) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) O)) = S.i₂
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hβ]
    exact hα

/-- For the original group model, its proper generic fibre is derived
from its actual generic identification. Thus properness at all maximal
localizations suffices without a new generic-properness premise. -/
theorem propernessFromMaximalLocalizations {K : Type} [Field K]
    {A : _root_.PkgI3.AbVar K} {F : Type} [Field F] [NumberField F] [Algebra K F]
    (𝒢 : _root_.ZInQ.DefFaltings.GroupModel A F)
    (hLocal : ∀ (𝔭 : Ideal (𝓞 F)) [𝔭.IsMaximal],
      IsProper (_root_.ReductGlue.toO 𝒢 (_root_.ReductGlue.dvrAt 𝔭)).G.hom) :
    IsProper 𝒢.G.hom := by
  have hGeneric : IsProper (_root_.ZInQ.DefFaltings.genericFibre F 𝒢.G).hom := by
    have hComp : IsProper (𝒢.gen.hom.left ≫ (A.baseChange F).X.hom) := inferInstance
    rw [Over.w 𝒢.gen.hom] at hComp
    exact hComp
  change IsProper (pullback.snd 𝒢.G.hom
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F)))) at hGeneric
  apply isProper_of_generic_and_maximal_localizations F 𝒢.G.hom hGeneric
  intro 𝔭 h𝔭
  exact hLocal 𝔭

end HDec.CMSerreTate.P4
