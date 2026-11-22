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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal.lean
  Source sha256  : 08c3ae34e17fd240ed2a9218f6bc9dffbab9ee28ad1979ff948d2241e8f5b48b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 7 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T7×2, T6×1; rule citations in the batch ledger.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Sites.Representability
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isRepresentable_supportedIn
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
r2nos_erase_attr "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry"

open AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.RelEffCartierDiv _root_.AlgebraicGeometry in
r2nos_open_dual "AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.RelEffCartierDiv" in
theorem solution
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by
  classical

  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨RelEffCartierDiv.functor f r, (isSheaf_iff_isSheaf_of_type _ _).2 (RelEffCartierDiv.isSheaf_functor f r)⟩

  let ι : Type u := Σ V : S.affineOpens, {U : 𝒞.affineOpens // (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)}
  have hrep : ∀ i : ι, ∃ X : Scheme.{u},
      Nonempty ((RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor.RepresentableBy X) :=
    fun i => by
      obtain ⟨X, -, hX⟩ := RelEffCartierDiv.isRepresentable_supportedIn f r i.1 i.2.1 i.2.2
      exact ⟨X, hX⟩
  choose X hX using hrep
  let e : ∀ i : ι, yoneda.obj (X i) ≅ (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor :=
    fun i => Functor.representableByEquiv (hX i).some
  let fam : ∀ i : ι, yoneda.obj (X i) ⟶ F.1 :=
    fun i => (e i).hom ≫ (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).ι

  have hfam : ∀ i, IsOpenImmersion.presheaf (fam i) := fun i =>
    (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
      (RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl f r _)

  haveI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc fam) := by
    constructor
    rintro T ⟨g, D⟩
    rw [Scheme.mem_grothendieckTopology_iff]
    choose W hW V U hUV hsupp using
      fun t : T => RelEffCartierDiv.exists_supportedIn_of_forall_finset f hcov r D t
    refine ⟨Scheme.Cover.mkOfCovers T (fun t => (W t : Scheme.{u})) (fun t => (W t).ι)
      (fun t => ⟨t, ⟨t, hW t⟩, rfl⟩) (fun t => inferInstance), ?_⟩
    rintro Y q ⟨t⟩

    let i : ι := ⟨V t, ⟨U t, hUV t⟩⟩
    let sec : (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor.obj (op (W t : Scheme.{u})) :=
      ⟨(RelEffCartierDiv.functor f r).map (W t).ι.op ⟨g, D⟩, hsupp t⟩
    refine ⟨(Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec), ?_⟩
    have h1 : (Limits.Sigma.desc fam).app (op (W t : Scheme.{u}))
        ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec)) =
        (fam i).app _ ((e i).inv.app _ sec) := by
      rw [← types_comp_apply ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _)
          ((Limits.Sigma.desc fam).app _),
        ← NatTrans.comp_app, Limits.Sigma.ι_desc]
    change (Limits.Sigma.desc fam).app (op (W t : Scheme.{u}))
        ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec)) =
      (RelEffCartierDiv.functor f r).map (W t).ι.op ⟨g, D⟩
    rw [h1]
    change ((e i).inv.app _ ≫ (e i).hom.app _ ≫ (RelEffCartierDiv.supportedIn f r _).ι.app _) sec = _
    rw [Iso.inv_hom_id_app_assoc]
    rfl

  have hR : (RelEffCartierDiv.functor f r).IsRepresentable :=
    Scheme.LocalRepresentability.isRepresentable hfam
  exact (RelEffCartierDiv.isRepresentable_functor_iff f r).1 hR
end S_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
