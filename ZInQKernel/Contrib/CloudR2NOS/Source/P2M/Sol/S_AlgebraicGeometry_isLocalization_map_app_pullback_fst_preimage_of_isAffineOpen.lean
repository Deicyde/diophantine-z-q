/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen.lean
  Source sha256  : 2baf07b152ee76e78eb49fa7654355c3ee9110fe01b4ddf36342a5f5894e0a7d
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace"
open TensorProduct
r2nos_open_dual "TensorProduct"

universe u

theorem solution
    {R : Type u} [CommRing R] (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
    {B : Scheme.{u}} (q : B ⟶ Spec (CommRingCat.of R)) (V : B.Opens) (hV : IsAffineOpen V) :
    letI := ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T)))).app V).hom.toAlgebra
    IsLocalization
      (M.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop ≫
          B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom : R →* Γ(B, V)))
      Γ(pullback q (Spec.map (CommRingCat.ofHom (algebraMap R T))),
        pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⁻¹ᵁ V) := by

  let ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R T))
  letI algB : Algebra R Γ(B, V) := Scheme.TwoAffineOpenCover.algebraOfHom q V
  letI algP : Algebra Γ(B, V) Γ(pullback q ι, pullback.fst q ι ⁻¹ᵁ V) :=
    ((pullback.fst q ι).app V).hom.toAlgebra

  letI algRP : Algebra R Γ(pullback q ι, pullback.fst q ι ⁻¹ᵁ V) :=
    Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst q ι ≫ q) (pullback.fst q ι ⁻¹ᵁ V)
  show IsLocalization (Algebra.algebraMapSubmonoid Γ(B, V) M) Γ(pullback q ι, pullback.fst q ι ⁻¹ᵁ V)

  haveI hT : IsLocalization (Algebra.algebraMapSubmonoid Γ(B, V) M) (Γ(B, V) ⊗[R] T) :=
    IsLocalization.tensor T M

  obtain ⟨ε, -, hε, -, -⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen R q T
  let e : Γ(pullback q ι, pullback.fst q ι ⁻¹ᵁ V) ≃ₐ[Γ(B, V)] (Γ(B, V) ⊗[R] T) :=
    AlgEquiv.ofRingEquiv (f := (ε V hV).toRingEquiv) (fun a => by
      change ε V hV (((pullback.fst q ι).app V).hom a) = a ⊗ₜ[R] (1 : T)
      exact hε V hV a)

  exact IsLocalization.isLocalization_of_algEquiv _ e.symm
end S_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
