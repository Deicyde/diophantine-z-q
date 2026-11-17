/-
NEW EDITION (H5 lane C4, 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.lean
  Source sha256  : 80fa409d52f17d462e015f0b420f5300025eb5c27376ff1547cce3629116ec5c
  Retrieved      : pinned read-only clone the upstream FLT repository (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

namespace N3da397ad0
r2nos_namespace_dual

section Topology

variable {α : Type*} [TopologicalSpace α]

theorem isPreirreducible_union_of_isOpen_of_mem {s U : Set α}
    (hs : IsPreirreducible s) (hU : IsPreirreducible U) (hUopen : IsOpen U)
    {y : α} (hys : y ∈ s) (hyU : y ∈ U) : IsPreirreducible (s ∪ U) := by
  have key : ∀ w : Set α, IsOpen w → ((s ∪ U) ∩ w).Nonempty → (U ∩ w).Nonempty := by
    rintro w hw ⟨z, hz, hzw⟩
    rcases hz with hzs | hzU
    · obtain ⟨t, hts, htw, htU⟩ := hs w U hw hUopen ⟨z, hzs, hzw⟩ ⟨y, hys, hyU⟩
      exact ⟨t, htU, htw⟩
    · exact ⟨z, hzU, hzw⟩
  rintro a b ha hb hane hbne
  obtain ⟨t, htU, htab⟩ := hU a b ha hb (key a ha hane) (key b hb hbne)
  exact ⟨t, Or.inr htU, htab⟩

theorem isOpen_irreducibleComponent_of_forall_isPreirreducible_nhd
    (hloc : ∀ y : α, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ IsPreirreducible U) (x : α) :
    IsOpen (irreducibleComponent x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨U, hUopen, hyU, hUirr⟩ := hloc y
  have hunion : IsPreirreducible (irreducibleComponent x ∪ U) :=
    isPreirreducible_union_of_isOpen_of_mem isIrreducible_irreducibleComponent.2 hUirr hUopen
      hy hyU
  have hsubset : U ⊆ irreducibleComponent x := by
    have heq : irreducibleComponent x ∪ U = irreducibleComponent x :=
      eq_irreducibleComponent hunion Set.subset_union_left
    rw [← heq]
    exact Set.subset_union_right
  exact Filter.mem_of_superset (hUopen.mem_nhds hyU) hsubset

theorem connectedComponent_eq_irreducibleComponent_of_forall_isPreirreducible_nhd
    (hloc : ∀ y : α, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ IsPreirreducible U) (x : α) :
    connectedComponent x = irreducibleComponent x := by
  have hclopen : IsClopen (irreducibleComponent x) :=
    ⟨isClosed_irreducibleComponent,
      isOpen_irreducibleComponent_of_forall_isPreirreducible_nhd hloc x⟩
  apply Set.Subset.antisymm
  · exact isPreconnected_connectedComponent.subset_isClopen hclopen
      ⟨x, mem_connectedComponent, mem_irreducibleComponent⟩
  · exact isIrreducible_irreducibleComponent.2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent

theorem isPreirreducible_connectedComponent_of_forall_isPreirreducible_nhd
    (hloc : ∀ y : α, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ IsPreirreducible U) (x : α) :
    IsPreirreducible (connectedComponent x) := by
  rw [connectedComponent_eq_irreducibleComponent_of_forall_isPreirreducible_nhd hloc x]
  exact isIrreducible_irreducibleComponent.2

end Topology

section Ring

variable {R : Type u} [CommRing R]

theorem eq_of_mem_minimalPrimes_of_le_of_isDomain_localizationAtPrime
    {p : Ideal R} [hp : p.IsPrime] (hdom : IsDomain (Localization.AtPrime p))
    {q₁ q₂ : Ideal R} (h₁ : q₁ ∈ minimalPrimes R) (h₂ : q₂ ∈ minimalPrimes R)
    (hle₁ : q₁ ≤ p) (hle₂ : q₂ ≤ p) : q₁ = q₂ := by
  haveI := hdom
  have hq₀p : (Ideal.comap (algebraMap R (Localization.AtPrime p))
      (⊥ : Ideal (Localization.AtPrime p))).IsPrime :=
    Ideal.IsPrime.comap (algebraMap R (Localization.AtPrime p))
  have hker_le : ∀ q : Ideal R, q.IsPrime → q ≤ p →
      Ideal.comap (algebraMap R (Localization.AtPrime p))
        (⊥ : Ideal (Localization.AtPrime p)) ≤ q := by
    intro q hq hqp
    have hdisj : Disjoint ((p.primeCompl : Set R)) ((q : Set R)) :=
      Set.disjoint_left.mpr fun a ha haq => Ideal.mem_primeCompl_iff.mp ha (hqp haq)
    have hcm : Ideal.comap (algebraMap R (Localization.AtPrime p))
        (Ideal.map (algebraMap R (Localization.AtPrime p)) q) = q :=
      IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl (Localization.AtPrime p)
        hq hdisj
    exact le_of_le_of_eq (Ideal.comap_mono bot_le) hcm
  have e₁ : q₁ = Ideal.comap (algebraMap R (Localization.AtPrime p))
      (⊥ : Ideal (Localization.AtPrime p)) :=
    le_antisymm (h₁.2 ⟨hq₀p, bot_le⟩ (hker_le q₁ h₁.1.1 hle₁)) (hker_le q₁ h₁.1.1 hle₁)
  have e₂ : q₂ = Ideal.comap (algebraMap R (Localization.AtPrime p))
      (⊥ : Ideal (Localization.AtPrime p)) :=
    le_antisymm (h₂.2 ⟨hq₀p, bot_le⟩ (hker_le q₂ h₂.1.1 hle₂)) (hker_le q₂ h₂.1.1 hle₂)
  rw [e₁, e₂]

theorem exists_mem_zeroLocus_minimalPrimes (x : PrimeSpectrum R) :
    ∃ q ∈ minimalPrimes R, x ∈ PrimeSpectrum.zeroLocus (q : Set R) := by
  obtain ⟨q, hq, hle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := x.asIdeal) bot_le
  exact ⟨q, hq, (PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr hle)⟩

theorem compl_zeroLocus_eq_biUnion
    (huniq : ∀ q₁ q₂ : Ideal R, q₁ ∈ minimalPrimes R → q₂ ∈ minimalPrimes R →
      ∀ p : Ideal R, p.IsPrime → q₁ ≤ p → q₂ ≤ p → q₁ = q₂)
    {q₀ : Ideal R} (hq₀ : q₀ ∈ minimalPrimes R) :
    (PrimeSpectrum.zeroLocus (q₀ : Set R))ᶜ
      = ⋃ q ∈ minimalPrimes R \ {q₀}, PrimeSpectrum.zeroLocus ((q : Ideal R) : Set R) := by
  ext x
  simp only [Set.mem_compl_iff]
  constructor
  · intro hx
    obtain ⟨q, hq, hxq⟩ := exists_mem_zeroLocus_minimalPrimes x
    have hne : q ≠ q₀ := by
      rintro rfl
      exact hx hxq
    exact Set.mem_biUnion ⟨hq, hne⟩ hxq
  · intro hx hx₀
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
    exact hq.2 (huniq q q₀ hq.1 hq₀ x.asIdeal x.isPrime
      (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hxq))
      (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hx₀)))

theorem isClopen_zeroLocus_of_mem_minimalPrimes [IsNoetherianRing R]
    (huniq : ∀ q₁ q₂ : Ideal R, q₁ ∈ minimalPrimes R → q₂ ∈ minimalPrimes R →
      ∀ p : Ideal R, p.IsPrime → q₁ ≤ p → q₂ ≤ p → q₁ = q₂)
    {q₀ : Ideal R} (hq₀ : q₀ ∈ minimalPrimes R) :
    IsClopen (PrimeSpectrum.zeroLocus (q₀ : Set R)) := by
  refine ⟨PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
  rw [← isClosed_compl_iff, compl_zeroLocus_eq_biUnion huniq hq₀]
  exact Set.Finite.isClosed_biUnion
    (Set.Finite.subset (minimalPrimes.finite_of_isNoetherianRing R) Set.diff_subset)
    (fun q _ => PrimeSpectrum.isClosed_zeroLocus _)

theorem exists_isClopen_isPreirreducible_mem_of_forall_isDomain_localizationAtPrime
    [IsNoetherianRing R]
    (hstalk : ∀ (p : Ideal R) [p.IsPrime], IsDomain (Localization.AtPrime p))
    (x : PrimeSpectrum R) :
    ∃ s : Set (PrimeSpectrum R), IsClopen s ∧ x ∈ s ∧ IsPreirreducible s := by
  have huniq : ∀ q₁ q₂ : Ideal R, q₁ ∈ minimalPrimes R → q₂ ∈ minimalPrimes R →
      ∀ p : Ideal R, p.IsPrime → q₁ ≤ p → q₂ ≤ p → q₁ = q₂ := by
    intro q₁ q₂ h₁ h₂ p hp hle₁ hle₂
    haveI := hp
    exact eq_of_mem_minimalPrimes_of_le_of_isDomain_localizationAtPrime (hstalk p) h₁ h₂ hle₁ hle₂
  obtain ⟨q₀, hq₀, hxq₀⟩ := exists_mem_zeroLocus_minimalPrimes x
  refine ⟨PrimeSpectrum.zeroLocus (q₀ : Set R), isClopen_zeroLocus_of_mem_minimalPrimes huniq hq₀, hxq₀, ?_⟩
  have hq₀p : q₀.IsPrime := hq₀.1.1
  have hirr : IsIrreducible (PrimeSpectrum.zeroLocus (q₀ : Set R)) := by
    rw [PrimeSpectrum.isIrreducible_zeroLocus_iff]
    rwa [hq₀p.radical]
  exact hirr.2

end Ring

section SchemeTransport

theorem isDomain_localizationAtPrime_of_isLocalization {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization p.primeCompl S] [IsDomain S] :
    IsDomain (Localization.AtPrime p) :=
  MulEquiv.isDomain S
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).toRingEquiv.toMulEquiv

theorem exists_primeIdealOf_eq {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    ∃ y : ↥U, hU.primeIdealOf y = p := by
  refine ⟨hU.isoSpec.inv p, ?_⟩
  show hU.isoSpec.hom (hU.isoSpec.inv p) = p
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  first
    | rfl
    | simp [Scheme.id_base]

theorem exists_isOpen_mem_isPreirreducible_of_forall_isDomain_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hstalk : ∀ x : ↥X, IsDomain (X.presheaf.stalk x)) (x : ↥X) :
    ∃ s : Set ↥X, IsOpen s ∧ x ∈ s ∧ IsPreirreducible s := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  haveI hnoeth : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hloc : ∀ (p : Ideal Γ(X, U)) [p.IsPrime], IsDomain (Localization.AtPrime p) := by
    intro p hp
    obtain ⟨y, hy⟩ := exists_primeIdealOf_eq hU ⟨p, hp⟩
    haveI hL := hU.isLocalization_stalk y
    haveI hD := hstalk y.1
    have hdom : IsDomain (Localization.AtPrime (hU.primeIdealOf y).asIdeal) :=
      isDomain_localizationAtPrime_of_isLocalization
        (hU.primeIdealOf y).asIdeal (X.presheaf.stalk y.1)
    rw [hy] at hdom
    exact hdom
  obtain ⟨s, hsclopen, hsmem, hspre⟩ :=
    exists_isClopen_isPreirreducible_mem_of_forall_isDomain_localizationAtPrime
      hloc (hU.primeIdealOf ⟨x, hxU⟩)
  refine ⟨⇑hU.fromSpec '' s, ?_, ?_, ?_⟩
  · exact (Scheme.Hom.isOpenEmbedding hU.fromSpec).isOpenMap _ hsclopen.isOpen
  · exact ⟨hU.primeIdealOf ⟨x, hxU⟩, hsmem, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  · exact hspre.image _ (Scheme.Hom.continuous hU.fromSpec).continuousOn

theorem isPreirreducible_connectedComponent_of_forall_isDomain_stalk
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    (hstalk : ∀ x : ↥T, IsDomain (T.presheaf.stalk x)) (x : ↥T) :
    IsPreirreducible (connectedComponent x) :=
  isPreirreducible_connectedComponent_of_forall_isPreirreducible_nhd
    (exists_isOpen_mem_isPreirreducible_of_forall_isDomain_stalk T hstalk) x

end SchemeTransport

end N3da397ad0

theorem solution
    (X : Scheme.{u}) [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hpre : IsPreirreducible (Set.univ : Set X) := by
    rw [← PreconnectedSpace.connectedComponent_eq_univ x]
    exact N3da397ad0.isPreirreducible_connectedComponent_of_forall_isDomain_stalk X h x
  haveI : IrreducibleSpace X := { isPreirreducible_univ := hpre, toNonempty := ⟨x⟩ }
  haveI : ∀ y : X, _root_.IsReduced (X.presheaf.stalk y) := fun y => inferInstance
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  exact (isIntegral_iff_irreducibleSpace_and_isReduced X).mpr ⟨inferInstance, inferInstance⟩

#print axioms solution
end S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
