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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit.lean
  Source sha256  : 904bf4c5a09e43bea6ae2f4ad6126c42dea657655bf039d7859109dff6429609
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 11 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
r2nos_namespace_dual
r2nos_erase_attr "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
r2nos_erase_attr "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) := by
  haveI : IsProper f := hJ.proper

  have hlqf : LocallyQuasiFinite (L.schemeNsmul n) := by
    refine AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo f
      (L.schemeNsmul n) (L.schemeNsmul_over n) ?_
    intro s
    rw [← RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo L s n]
    have hfib := GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr hJ s
    haveI : Smooth (RelativeGroupLaw.fibreStr f s) := hfib.smooth
    haveI : LocallyOfFiniteType (RelativeGroupLaw.fibreStr f s) := inferInstance
    have hu : IsUnit ((n : ℕ) : RelativeGroupLaw.baseResidueField s) := by
      have h := hn.map (((Spec (CommRingCat.of R)).Γevaluation s).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      simpa only [map_natCast] using h
    exact RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit (L.fibre s)
      (fun t' x y => RelativeGroupLaw.fibre_mul_comm L hcomm s t' x y) n hu
  haveI := hlqf
  haveI : IsProper (L.schemeNsmul n) := by
    have : IsProper (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]; infer_instance
    exact IsProper.of_comp _ f
  have hfin : IsFinite (L.schemeNsmul n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  refine ⟨hfin, ?_⟩

  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have h01 : (0 : R) = 1 := isUnit_zero_iff.mp (by simpa using hn)
    haveI : Subsingleton R := subsingleton_of_zero_eq_one h01
    haveI : IsEmpty (Spec (CommRingCat.of R) : Scheme.{u}) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum R))
    haveI : IsEmpty J := Function.isEmpty f.base
    infer_instance
  · exact RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle L hJ
      (fun t x y => hcomm t x y) n hpos hfin
end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
