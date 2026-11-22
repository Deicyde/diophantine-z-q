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
  Source file    : P2M/Sol/S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField.lean
  Source sha256  : 64660697a901b37371433d4e11ff4cabec5b6270ec733593549bdbc52fe6d775
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
r2nos_namespace_dual
set_option autoImplicit false
open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"
universe u v w

namespace F2aux
r2nos_namespace_dual

scoped instance isReduced_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsReduced : ObjectProperty Scheme.{u}) where
  of_iso e _ := isReduced_of_isOpenImmersion e.inv

lemma isReduced_pullback_Spec {k : Type u} [Field k] [PerfectField k]
    {R : CommRingCat.{u}} (g : Spec R ⟶ Spec (CommRingCat.of k)) (hred : IsReduced (Spec R))
    (hft : LocallyOfFiniteType g) (K : Type u) [Field K] [Algebra k K] :
    IsReduced (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  have hft' : Algebra.FiniteType k R := by
    rw [← RingHom.finiteType_algebraMap]
    exact HasRingHomProperty.Spec_iff.mp hft
  have hred' : _root_.IsReduced R := (affine_isReduced_iff R).mp hred
  have hKR : _root_.IsReduced (K ⊗[k] R) :=
    Algebra.TensorProduct.isReduced_of_perfectField_of_isReduced k R K
  have hRK : _root_.IsReduced (R ⊗[k] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k R K).toRingHom
      (Algebra.TensorProduct.comm k R K).injective
  have : IsReduced (Spec (CommRingCat.of (R ⊗[k] K))) := (affine_isReduced_iff _).mpr hRK
  let e : pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      Spec (CommRingCat.of (R ⊗[k] K)) :=
    pullbackSpecIso k R K
  exact isReduced_of_isOpenImmersion e.hom

end F2aux
w03_reactivate "P2MW.S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField.F2aux"

theorem solution {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced X] :
    GeometricallyReduced f := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms (P := IsReduced)).mpr ?_⟩
  intro K _ _

  apply +allowSynthFailures @IsReduced.of_openCover
    (𝒰 := Scheme.Pullback.openCoverOfLeft X.affineCover f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  intro i
  rw [Scheme.Pullback.openCoverOfLeft_X]

  have hred : IsReduced (X.affineCover.X i) := isReduced_of_isOpenImmersion (X.affineCover.f i)
  have hft : LocallyOfFiniteType (X.affineCover.f i ≫ f) := inferInstance
  exact F2aux.isReduced_pullback_Spec (X.affineCover.f i ≫ f) hred hft K
end S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
