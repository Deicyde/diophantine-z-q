/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 6 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 2 `attribute [-instance]/[-simp]` performance-guard line(s) removed.
  * 1 scope(s) the source leaves open at EOF closed explicitly (end P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
  * one `w03_open "AlgebraicGeometry"` inserted after the port namespace: this file `open`s `AlgebraicGeometry`, which the port also declares as nested namespace(s), so a
    plain `open` would resolve to the nested one and hide Mathlib's. The dual root+prefix
    shim keeps the Mathlib root namespace(s) visible, exactly as in the original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "AlgebraicGeometry"

namespace P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) :
    NeronModelInfra.NeronModelPropertyBundle R K f := by
  haveI : IsProper f := hA.proper
  have hsep : IsSeparated f := inferInstance
  refine ⟨hA.smooth, hsep, inferInstance, inferInstance, ?_⟩
  refine neronUniqueExtension_of_forall_quasiCompact R K f fun T t ht hqc => ?_
  haveI := ht
  haveI := hqc
  haveI : Flat t := inferInstance
  exact ⟨genericFibreRestrict_injective_of_flat_of_isSeparated R K f t,
    hA.genericFibreRestrict_surjective_of_quasiCompact R K t⟩

end P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle

end ZInQ.Contrib.CloudW03NeronSurj.FLT
