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
  Source file    : P2M/Sol/S_AlgebraicGeometry_isReduced_of_smooth_over_field.lean
  Source sha256  : 808fc49279379e7774fbdde7cb379d3f93eab37d9292a3aa6cd68b7a69ed8672
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_isReduced_of_smooth_over_field
r2nos_namespace_dual

set_option autoImplicit false

universe u

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace IsReducedOfSmoothFieldAux
r2nos_namespace_dual

theorem etale_isReduced (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] : IsReduced A := by
  haveI : Algebra.FormallyUnramified K A := inferInstance
  haveI : Algebra.EssFiniteType K A := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K A

theorem isStandardSmooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.IsStandardSmooth) : IsReduced A := by
  obtain ⟨n, g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin n) R) A := g.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) A := hg.toAlgebra
  haveI : IsReduced
      (FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A) :=
    IsReducedOfSmoothFieldAux.etale_isReduced (FractionRing (MvPolynomial (Fin n) R)) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight :
      A →ₐ[MvPolynomial (Fin n) R]
        FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A)
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective (MvPolynomial (Fin n) R)
        (FractionRing (MvPolynomial (Fin n) R))))

theorem smooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.Smooth) : IsReduced A := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth] at hφ
  obtain ⟨s, hs, H⟩ := hφ
  constructor
  intro x hx
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  rw [map_zero]
  funext a
  haveI : IsReduced (Localization.Away a.1) :=
    IsReducedOfSmoothFieldAux.isStandardSmooth_isReduced_of_isDomain (H a.1 a.2)
  simpa using IsReduced.eq_zero _ (hx.map (algebraMap A (Localization.Away a.1)))

end IsReducedOfSmoothFieldAux

section SchemeLevel

open AlgebraicGeometry CategoryTheory
r2nos_open_dual "AlgebraicGeometry CategoryTheory"

theorem solution {k : Type u} [Field k]
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) : IsReduced Z := by
  haveI := hg
  haveI : ∀ i, IsReduced (Z.affineCover.X i) := by
    intro i
    haveI : IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
      Function.Injective.isDomain _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    haveI : _root_.IsReduced ↑Γ(Z.affineCover.X i, ⊤) :=
      IsReducedOfSmoothFieldAux.smooth_isReduced_of_isDomain
        ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp
          (inferInstance : Smooth (Z.affineCover.f i ≫ g)))
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ Z.affineCover

end SchemeLevel

#print axioms solution
end S_AlgebraicGeometry_isReduced_of_smooth_over_field
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
