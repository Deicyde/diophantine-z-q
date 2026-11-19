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
  Source file    : P2M/Sol/S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one.lean
  Source sha256  : 5095a530ce005f2a2b83f1c551c83c96af0662b0e5d953a6f15acf50e8b5ea99
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
r2nos_namespace_dual

set_option autoImplicit false

open AlgebraicGeometry TopologicalSpace CategoryTheory
r2nos_open_dual "AlgebraicGeometry TopologicalSpace CategoryTheory"

universe u

theorem solution {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] : ¬ IsAffine X := by
  intro hX
  haveI : IsAffineHom f := isAffineHom_of_isAffine f
  haveI hfin : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

  have hΓ : (f.appTop).hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)

  let φ : k →+* Γ(X, ⊤) := (f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφfin : φ.Finite :=
    RingHom.Finite.comp hΓ (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have hfield : IsField Γ(X, ⊤) := by
    letI := φ.toAlgebra
    haveI : Module.Finite k Γ(X, ⊤) := hφfin
    haveI : Algebra.IsIntegral k Γ(X, ⊤) := Algebra.IsIntegral.of_finite k _
    exact (Algebra.IsIntegral.isField_iff_isField (R := k) (S := Γ(X, ⊤)) φ.injective).mp
      (Field.toIsField k)

  have hsub : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := by
    haveI := Ring.isField_iff_isSimpleOrder_ideal.mp hfield
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    rcases IsSimpleOrder.eq_bot_or_eq_top p.asIdeal with hp | hp
    · rcases IsSimpleOrder.eq_bot_or_eq_top q.asIdeal with hq | hq
      · rw [hp, hq]
      · exact absurd hq q.isPrime.ne_top
    · exact absurd hp p.isPrime.ne_top
  have hsubX : Subsingleton X := by
    haveI : Subsingleton (Spec Γ(X, ⊤)) := hsub
    exact (Scheme.homeoOfIso X.isoSpec).toEquiv.subsingleton
  have hclosed : IsClosed ({genericPoint X} : Set X) := by
    have : ({genericPoint X} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [this]; exact isClosed_univ

  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk (genericPoint X)) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f
      (genericPoint X) hclosed
  exact IsDiscreteValuationRing.not_isField (X.presheaf.stalk (genericPoint X))
    (Field.toIsField X.functionField)
end S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
