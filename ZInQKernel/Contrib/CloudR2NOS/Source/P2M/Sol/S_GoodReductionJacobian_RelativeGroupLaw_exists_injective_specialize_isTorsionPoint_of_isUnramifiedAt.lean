/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt.lean
  Source sha256  : d856ea3ce213affcdcd390764ccff97c6041515c632b2e0bf7091a5987a60bf3
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option linter.unusedSectionVars false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt.GoodReductionJacobian"
open scoped nonZeroDivisors
r2nos_open_scoped_dual "nonZeroDivisors"

universe u

namespace GoodReductionJacobian
r2nos_namespace_dual
w03_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_smooth"
namespace RelativeGroupLaw
r2nos_namespace_dual
w03_export "GoodReductionJacobian.RelativeGroupLaw" "mul IsTorsionPoint genericFibre fibre exists_injective_specialize_isTorsionPoint_of_smooth"
namespace TorsionSpecializationDedekind
r2nos_namespace_dual
w03_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section EtaleNbhd

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]

theorem exists_formallyUnramified_away :
    ∃ f : S, f ∉ P ∧ Algebra.FormallyUnramified R (Localization.Away f) := by
  have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S := by
    change Algebra.IsUnramifiedAt R P
    infer_instance
  obtain ⟨v, ⟨f, rfl⟩, hfv, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem
      Algebra.isOpen_unramifiedLocus
  refine ⟨f, ?_, Algebra.basicOpen_subset_unramifiedLocus_iff.mp hsub⟩
  simpa using hfv

variable (f : S)

theorem smooth_specMap_away [Algebra.FormallyUnramified R (Localization.Away f)] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  haveI : Module.Flat R (Localization.Away f) := Module.Flat.trans R S (Localization.Away f)
  haveI : Algebra.FiniteType R (Localization.Away f) :=
    Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  haveI : Algebra.FinitePresentation R (Localization.Away f) :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI : Algebra.Etale R (Localization.Away f) := Algebra.Etale.of_formallyUnramified_of_flat
  haveI : Algebra.Smooth R (Localization.Away f) := inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (Localization.Away f)).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

end EtaleNbhd

section GenericFibre

variable (R : Type u) [CommRing R] [IsDomain R]
  (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
  (L : Type u) [Field L] [Algebra S L] [Algebra R L]
  [IsScalarTower R S L] [IsFractionRing S L] [IsIntegralClosure S R L]
  (f : S) (hf : f ≠ 0)

noncomputable def awayToField : Localization.Away f →+* L :=
  IsLocalization.Away.lift f (g := algebraMap S L)
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hf))

theorem awayToField_comp : (awayToField S L f hf).comp (algebraMap S (Localization.Away f)) = algebraMap S L :=
  IsLocalization.Away.lift_comp f _

theorem awayToField_injective : Function.Injective (awayToField S L f hf) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
  have h := IsLocalization.mk'_spec (Localization.Away f) s m
  have h' := congrArg (awayToField S L f hf) h
  rw [map_mul, hx, zero_mul, ← RingHom.comp_apply, awayToField_comp] at h'
  have hs : s = 0 := (map_eq_zero_iff _ (IsFractionRing.injective S L)).mp h'.symm
  subst hs
  change IsLocalization.mk' (Localization.Away f) 0 m = 0
  exact IsLocalization.mk'_zero _

theorem isLocalization_away (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [IsScalarTower R K L] [Algebra.IsAlgebraic K L] :
    letI : Algebra (Localization.Away f) L := (awayToField S L f hf).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away f) R⁰) L := by
  letI : Algebra (Localization.Away f) L := (awayToField S L f hf).toAlgebra
  have halg : ∀ x, algebraMap (Localization.Away f) L x = awayToField S L f hf x := fun _ => rfl
  haveI hSL : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization R K L S
  have htower : ∀ s : S, algebraMap (Localization.Away f) L (algebraMap S _ s) = algebraMap S L s := by
    intro s; rw [halg, ← RingHom.comp_apply, awayToField_comp]
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    change IsUnit (algebraMap (Localization.Away f) L (algebraMap R (Localization.Away f) r))
    rw [IsScalarTower.algebraMap_apply R S (Localization.Away f), htower]
    exact IsLocalization.map_units L (M := Algebra.algebraMapSubmonoid S R⁰)
      ⟨algebraMap R S r, r, hr, rfl⟩
  · intro y
    obtain ⟨⟨s, ⟨_, r, hr, rfl⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S R⁰) y
    refine ⟨⟨algebraMap S _ s, ⟨algebraMap R _ r, r, hr, rfl⟩⟩, ?_⟩
    change y * algebraMap (Localization.Away f) L (algebraMap R (Localization.Away f) r) =
      algebraMap (Localization.Away f) L (algebraMap S _ s)
    rw [IsScalarTower.algebraMap_apply R S (Localization.Away f), htower, htower]
    exact h
  · intro x₁ x₂ h
    rw [halg, halg] at h
    exact ⟨1, by rw [awayToField_injective S L f hf h]⟩

end GenericFibre

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem main (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (L : Type u) [Field L] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing S L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : S →ₐ[R] k')
    (hψ : ∀ s : S, ψ s = 0 → s ∈ P) :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r := by

  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective R S]
    intro a b h
    have h' := congrArg (algebraMap S L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at h'
    exact (IsFractionRing.injective R K) ((algebraMap K L).injective h')

  obtain ⟨f, hfP, hunr⟩ := exists_formallyUnramified_away R S P
  haveI := hunr
  have hf0 : f ≠ 0 := fun h => hfP (h ▸ P.zero_mem)
  let R' := Localization.Away f
  haveI : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) R'
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := smooth_specMap_away R S f

  letI : Algebra R' L := (awayToField S L f hf0).toAlgebra
  have halg : ∀ x, algebraMap R' L x = awayToField S L f hf0 x := fun _ => rfl
  haveI : IsScalarTower S R' L := IsScalarTower.of_algebraMap_eq (fun s => by
    rw [halg, ← RingHom.comp_apply, awayToField_comp])
  haveI : IsScalarTower R R' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R S R', ← IsScalarTower.algebraMap_apply S R' L,
      ← IsScalarTower.algebraMap_apply R S L])
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L := isLocalization_away R S L f hf0 K

  have hψf : IsUnit ((ψ : S →+* k') f) := isUnit_iff_ne_zero.mpr (fun h => hfP (hψ f h))
  let ψ₀ : R' →+* k' := IsLocalization.Away.lift f hψf
  have hψ₀ : ψ₀.comp (algebraMap S R') = (ψ : S →+* k') := IsLocalization.Away.lift_comp f hψf
  let ψ' : R' →ₐ[R] k' :=
    { ψ₀ with
      commutes' := fun r => by
        change ψ₀ (algebraMap R R' r) = algebraMap R k' r
        rw [IsScalarTower.algebraMap_apply R S R', ← RingHom.comp_apply, hψ₀]
        exact ψ.commutes r }
  obtain ⟨r, hr, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_smooth
      K LB hcomm hN n hn R' hsm L k' ψ'
  exact ⟨r, hr⟩

end Main

end GoodReductionJacobian.RelativeGroupLaw.TorsionSpecializationDedekind

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (L : Type u) [Field L] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing S L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : S →ₐ[R] k')
    (hψ : ∀ s : S, ψ s = 0 → s ∈ P) :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r :=
  GoodReductionJacobian.RelativeGroupLaw.TorsionSpecializationDedekind.main K LB hcomm hN n hn S L P k' ψ hψ
end S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
