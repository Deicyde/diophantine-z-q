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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective.lean
  Source sha256  : c6001aed2ef354ebad5283fff5c120db2ee81431f61fe688c14083f804983c68
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace SEPAuxFFX
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left (G := SchemeHomOver t' f) h

abbrev τ (f : G ⟶ Spec (CommRingCat.of R)) : pullback f f ⟶ Spec (CommRingCat.of R) := pullback.snd f f ≫ f

def pa (f : G ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (τ f) f := ⟨pullback.fst f f, pullback.condition⟩
def pb (f : G ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (τ f) f := ⟨pullback.snd f f, rfl⟩

def shearHom (L : RelativeGroupLaw R f) : pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.snd f f) (L.mul (τ f) (pa f) (pb f)).1 (by rw [(L.mul (τ f) (pa f) (pb f)).2])

def shearInv (L : RelativeGroupLaw R f) : pullback f f ⟶ pullback f f :=
  pullback.lift (L.mul (τ f) (pb f) (L.inv (τ f) (pa f))).1 (pullback.fst f f)
    (by rw [(L.mul (τ f) (pb f) (L.inv (τ f) (pa f))).2]; exact pullback.condition.symm)

@[scoped simp] theorem shearHom_fst (L : RelativeGroupLaw R f) : shearHom L ≫ pullback.fst f f = pullback.snd f f :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem shearHom_snd (L : RelativeGroupLaw R f) :
    shearHom L ≫ pullback.snd f f = (L.mul (τ f) (pa f) (pb f)).1 := pullback.lift_snd _ _ _
@[scoped simp] theorem shearInv_fst (L : RelativeGroupLaw R f) :
    shearInv L ≫ pullback.fst f f = (L.mul (τ f) (pb f) (L.inv (τ f) (pa f))).1 := pullback.lift_fst _ _ _
@[scoped simp] theorem shearInv_snd (L : RelativeGroupLaw R f) : shearInv L ≫ pullback.snd f f = pullback.fst f f :=
  pullback.lift_snd _ _ _

theorem shearHom_τ (L : RelativeGroupLaw R f) : shearHom L ≫ τ f = τ f := by
  show shearHom L ≫ pullback.snd f f ≫ f = pullback.snd f f ≫ f
  rw [← Category.assoc, shearHom_snd, (L.mul (τ f) (pa f) (pb f)).2]

theorem shearInv_τ (L : RelativeGroupLaw R f) : shearInv L ≫ τ f = τ f := by
  show shearInv L ≫ pullback.snd f f ≫ f = pullback.snd f f ≫ f
  rw [← Category.assoc, shearInv_snd, pullback.condition]

def shear (L : RelativeGroupLaw R f) : pullback f f ≅ pullback f f where
  hom := shearHom L
  inv := shearInv L
  hom_inv_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearHom L) (shearHom_τ L) (pa f) = pb f :=
      Subtype.ext (shearHom_fst L)
    have hb : GoodReductionJacobian.schemeHomOverComp (shearHom L) (shearHom_τ L) (pb f) = L.mul (τ f) (pa f) (pb f) :=
      Subtype.ext (shearHom_snd L)
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearInv_fst]
      have := congrArg Subtype.val
        (L.mul_natural (τ f) (τ f) (shearHom L) (shearHom_τ L) (pb f) (L.inv (τ f) (pa f)))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, inv_natural, ha, hb, L.mul_assoc, L.mul_inv_cancel, L.mul_one]
      rfl
    · rw [Category.id_comp, Category.assoc, shearInv_snd, shearHom_fst]
  inv_hom_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearInv L) (shearInv_τ L) (pa f) =
        L.mul (τ f) (pb f) (L.inv (τ f) (pa f)) := Subtype.ext (shearInv_fst L)
    have hb : GoodReductionJacobian.schemeHomOverComp (shearInv L) (shearInv_τ L) (pb f) = pa f :=
      Subtype.ext (shearInv_snd L)
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearHom_fst, shearInv_snd]
    · rw [Category.id_comp, Category.assoc, shearHom_snd]
      have := congrArg Subtype.val (L.mul_natural (τ f) (τ f) (shearInv L) (shearInv_τ L) (pa f) (pb f))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, ha, hb, L.mul_assoc, L.inv_mul_cancel, L.mul_one]
      rfl

theorem lift_snd_action_eq (L : RelativeGroupLaw R f) {N : Scheme.{u}} (i : N ⟶ G)
    (hst : pullback.snd (i ≫ f) f ≫ f = L.action i ≫ f) :
    pullback.lift (pullback.snd (i ≫ f) f) (L.action i) hst =
      pullback.map (i ≫ f) f f f i (𝟙 G) (𝟙 _) ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (shear L).hom := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
    show _ = _ ≫ shearHom L ≫ _
    rw [shearHom_fst, pullback.lift_snd, Category.comp_id]
  · rw [pullback.lift_snd, Category.assoc]
    show _ = _ ≫ shearHom L ≫ _
    rw [shearHom_snd]
    set m := pullback.map (i ≫ f) f f f i (𝟙 G) (𝟙 _) ((Category.comp_id _).trans rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    have hm : m ≫ τ f = GoodReductionJacobian.RelativeGroupLaw.actionSource f i := by
      show m ≫ pullback.snd f f ≫ f = pullback.snd (i ≫ f) f ≫ f
      rw [← Category.assoc, pullback.lift_snd, Category.comp_id]
    have := congrArg Subtype.val (L.mul_natural (τ f) (GoodReductionJacobian.RelativeGroupLaw.actionSource f i) m hm (pa f) (pb f))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
    rw [this, L.action_def]
    congr 2
    · apply Subtype.ext
      show pullback.fst (i ≫ f) f ≫ i = m ≫ pullback.fst f f
      exact (pullback.lift_fst _ _ _).symm
    · apply Subtype.ext
      show pullback.snd (i ≫ f) f = m ≫ pullback.snd f f
      exact ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

end SEPAuxFFX
w03_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective.SEPAuxFFX"

end
w03_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective.SEPAuxFFX"

open SEPAuxFFX in
r2nos_open_dual "SEPAuxFFX" in
theorem solution
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q) (hq : q ≫ fQ = f)
    [Flat q] [LocallyOfFinitePresentation q] [QuasiCompact q] [Surjective q]
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q) :
    IsSeparated fQ ∧ QuasiCompact fQ := by
  constructor
  ·
    subst hq
    have hst : pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ) ≫ q ≫ fQ = L.action i ≫ q ≫ fQ := by
      have := congrArg (fun φ => φ ≫ fQ) hR.w
      simpa only [Category.assoc] using this

    let π := pullback.map (q ≫ fQ) (q ≫ fQ) fQ fQ q q (𝟙 _) (Category.comp_id _) (Category.comp_id _)
    let ρ := pullback.map q q (q ≫ fQ) (q ≫ fQ) (𝟙 G) (𝟙 G) fQ (Category.id_comp _).symm (Category.id_comp _).symm
    have hΔ := pullback_map_diagonal_isPullback q q fQ
    haveI : Flat π := MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance rfl rfl
    haveI : QuasiCompact π := MorphismProperty.pullbackMap (P := @QuasiCompact) inferInstance inferInstance rfl rfl
    haveI : Surjective π := MorphismProperty.pullbackMap (P := @Surjective) inferInstance inferInstance rfl rfl
    have hquot := Flat.isQuotientMap_of_surjective π

    have h1 : Set.range ρ.base = π.base ⁻¹' Set.range (pullback.diagonal fQ).base := by
      have := AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback hΔ Set.univ
      simpa only [Set.preimage_univ, Set.image_univ] using this
    have h2 : pullback.lift (pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ)) (L.action i) hst = hR.isoPullback.hom ≫ ρ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd]
    haveI : IsClosedImmersion (pullback.lift (pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ)) (L.action i) hst) := by
      rw [lift_snd_action_eq L i hst]
      have : IsClosedImmersion (pullback.map (i ≫ q ≫ fQ) (q ≫ fQ) (q ≫ fQ) (q ≫ fQ) i (𝟙 G) (𝟙 _)
          ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans (Category.id_comp _).symm)) :=
        MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance rfl (Category.id_comp _).symm
      infer_instance
    have h3 : IsClosed (Set.range ρ.base) := by
      have hr : Set.range (pullback.lift (pullback.snd (i ≫ q ≫ fQ) (q ≫ fQ)) (L.action i) hst).base = Set.range ρ.base := by
        rw [h2, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (hR.isoPullback.hom.homeomorph.surjective).range_comp _
      rw [← hr]
      exact (Scheme.Hom.isClosedEmbedding _).isClosed_range
    have h4 : IsClosed (Set.range (pullback.diagonal fQ).base) := by
      rw [← hquot.isClosed_preimage, ← h1]; exact h3
    exact ⟨IsClosedImmersion.of_isPreimmersion _ h4⟩
  ·
    haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace Q := ⟨by rw [← Set.range_eq_univ.mpr q.surjective]; exact isCompact_range q.continuous⟩
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹_›

#print axioms solution
end S_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
