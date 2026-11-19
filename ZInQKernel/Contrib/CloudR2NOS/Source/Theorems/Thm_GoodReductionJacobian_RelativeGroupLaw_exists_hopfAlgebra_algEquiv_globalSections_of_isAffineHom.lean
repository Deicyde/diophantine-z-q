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
  Source file    : Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom.lean
  Source sha256  : ef48723e5fe8dc5d07e70b9515b326ceb6b91b9a1307602ebe89e02099ff1d62
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

r2nos_erase_attr "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
    {R : Type u} [CommRing R] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    [IsAffineHom g] [Flat g] [LocallyOfFiniteType g] :
    letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    haveI : IsAffine A := isAffine_of_isAffineHom g
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Algebra.FiniteType R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ (iso : H ≃ₐ[R] Γ(A, ⊤))
        (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
          (e T φ).1 =
            Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫ A.isoSpec.inv) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (σ : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (σ.comp φ.ofConv))).1 =
            Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e T φ).1) := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
