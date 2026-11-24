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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed.lean
  Source sha256  : 735add76862cfd0ceffa138319f67b1a67430665d27142d48ab808d736e51b67
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_split
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
r2nos_erase_attr "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "SmoothOfRelativeDimension pointOfClosedPoint LocallyOfFiniteType Spec Scheme LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp IsSeparated RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp prodKerGraph RelEffCartierDiv.exists_split prodKerGraph_comap_mapOnProdOver"
namespace SumPtsAux
r2nos_namespace_dual
end AlgebraicGeometry.SumPtsAux
r2nos_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [Nonempty X] :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ :=
    nonempty_inter_closedPoints (X := X) Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {k : Type u} [Field k] [IsAlgClosed k] {x : Spec (CommRingCat.of k) ⟶ S}
    {r : ℕ} (D : RelEffCartierDiv f r x) :
    ∃ (a : Fin r → (Spec (CommRingCat.of k) ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = x),
      D.I = prodKerGraph f a ha := by
  obtain ⟨P, gP, p, hp, b, hb, hfin, -, -, hsurj, -, hsplit, -⟩ := D.exists_split
  haveI : Nonempty P := by
    obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary _)
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed p
  have hu' : u ≫ gP = x := by rw [← hp, ← Category.assoc, hu, Category.id_comp]
  have key : D = (D.pullbackAlong p hp).pullbackAlong u hu' := by
    rw [RelEffCartierDiv.pullbackAlong_comp]
    have aux : ∀ (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ x = x),
        φ = 𝟙 _ → D.pullbackAlong φ hφ = D := by
      rintro φ hφ rfl
      exact D.pullbackAlong_id
    exact (aux _ _ hu).symm
  refine ⟨fun i => u ≫ b i, fun i => by rw [Category.assoc, hb, hu'], ?_⟩
  calc D.I = ((D.pullbackAlong p hp).pullbackAlong u hu').I := by rw [← key]
    _ = (D.pullbackAlong p hp).I.comap (mapOnProdOver f u hu') := rfl
    _ = (prodKerGraph f b hb).comap (mapOnProdOver f u hu') := by rw [hsplit]
    _ = prodKerGraph f (fun i => u ≫ b i) _ := prodKerGraph_comap_mapOnProdOver b hb u hu'
end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
