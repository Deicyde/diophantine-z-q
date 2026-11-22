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
  Source file    : P2M/Sol/S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.lean
  Source sha256  : 0dc82f76a9bde450ee94737f25340d03de0443814db3c0410dd486d9aa418740
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 8 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 13 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_PartialAction
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_PartialAction_exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
r2nos_erase_attr "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.GoodReductionJacobian"
open Topology
r2nos_open_dual "Topology"

universe u

namespace GoodReductionJacobian
r2nos_namespace_dual
w03_export "GoodReductionJacobian" "RelativeGroupLaw PartialAction PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one PartialAction.unitActs_and_assoc_of_compatible_of_maximal PartialAction.exists_stable_defined_one_of_closure_image_eq_closure_singleton RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex"
namespace PartialAction
r2nos_namespace_dual
w03_export "GoodReductionJacobian.PartialAction" "Defined UnitActs Assoc Compatible Maximal Stable dom exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one unitActs_and_assoc_of_compatible_of_maximal exists_stable_defined_one_of_closure_image_eq_closure_singleton"
namespace GoodModel
r2nos_namespace_dual
w03_open "GoodReductionJacobian.PartialAction GoodReductionJacobian"

section Group

variable {k : Type u} [Field k]

theorem irreducibleSpace_of_connectedSpace [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f) : IrreducibleSpace G := by
  obtain ⟨G₀, i, L₀, hoi, -, hirr, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      k L
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  exact hsurj.irreducibleSpace i.continuous

theorem isField_sections (k : Type u) [Field k] :
    IsField (Γ(Spec (CommRingCat.of k), ⊤) : Type u) :=
  MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

scoped instance isDomain_sections (k : Type u) [Field k] :
    IsDomain (Γ(Spec (CommRingCat.of k), ⊤) : Type u) :=
  (isField_sections k).isDomain

scoped instance isIntegrallyClosed_sections (k : Type u) [Field k] :
    IsIntegrallyClosed (Γ(Spec (CommRingCat.of k), ⊤) : Type u) := by
  letI : Field (Γ(Spec (CommRingCat.of k), ⊤) : Type u) := (isField_sections k).toField
  infer_instance

private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.PartialAction.GoodModel.isDomain_and_isIntegrallyClosed_stalk {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [Smooth f] (x : G) :
    IsDomain (G.presheaf.stalk x) ∧ IsIntegrallyClosed (G.presheaf.stalk x) :=
  AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk f x

w03_export "GoodReductionJacobian.PartialAction.GoodModel" "isDomain_and_isIntegrallyClosed_stalk"

theorem isReduced_of_smooth {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    IsReduced G := by
  haveI : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x) := fun x => by
    haveI := (isDomain_and_isIntegrallyClosed_stalk f x).1
    infer_instance
  exact isReduced_of_isReduced_stalk G

theorem isIntegral_of_connectedSpace [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f) : IsIntegral G := by
  haveI := irreducibleSpace_of_connectedSpace f L
  haveI := isReduced_of_smooth f
  exact isIntegral_of_irreducibleSpace_of_isReduced G

theorem topologicalKrullDim_eq {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    [SmoothOfRelativeDimension g f] [Nonempty G] : topologicalKrullDim G = g :=
  le_antisymm (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le f g)
    (AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim f g)

end Group

section Assembly

theorem exists_model (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f] (hG : ¬ IsProper f) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k)) (V : G.Opens)
      (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) (a : PartialAction k f p)
      (W : Set ↥P) (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p),
      IsProper p ∧ IsIntegral P ∧ (∀ x : P, IsIntegrallyClosed (P.presheaf.stalk x)) ∧
      Nonempty (V : Scheme.{u}) ∧ IsOpenImmersion ι ∧
      a.Compatible L V ι hι ∧ a.Maximal ∧
      (∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom) ∧
      IsClosed W ∧ topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞) ∧ a.Stable W ∧
      P₀.1 (IsLocalRing.closedPoint k) ∈ W ∧
      a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth g f
  haveI : IsIntegral G := isIntegral_of_connectedSpace f L
  have hnG : ∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x) := fun x =>
    (isDomain_and_isIntegrallyClosed_stalk f x).2

  obtain ⟨P₁, p₁, D₁, τ₁, V₁, ι₁, hp₁, hP₁, hn₁, hτ₁, hτ₁f, hV₁, hι₁, hτι₁⟩ :=
    AlgebraicGeometry.exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
      k f hnG
  haveI := hp₁; haveI := hP₁; haveI := hτ₁; haveI := hV₁; haveI := hι₁

  obtain ⟨P₂, π, V₂, ι₂, hP₂, hn₂, hπ, hV₂, hι₂, hτι₂, w₂, hw₂, hw₂₁⟩ :=
    AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
      k f hG p₁ hn₁ D₁ τ₁ hτ₁f V₁ ι₁ hτι₁
  haveI := hP₂; haveI := hπ; haveI := hV₂; haveI := hι₂

  haveI hp₂ : IsProper (π ≫ p₁) := inferInstance
  haveI hτ₂ : IsProper ((π ∣_ D₁) ≫ τ₁) := inferInstance
  have hτ₂f : ((π ∣_ D₁) ≫ τ₁) ≫ f = (π ⁻¹ᵁ D₁).ι ≫ π ≫ p₁ := by
    rw [Category.assoc, hτ₁f, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hτι₂' : ι₂ ≫ ((π ∣_ D₁) ≫ τ₁) = V₂.ι := by rw [hτι₂]

  obtain ⟨P₃, π₃, V₃, ι₃, hι₃, a₃, w₃, w₃', hP₃, hn₃, hπ₃, hdim₃, hV₃, hι₃o, hc₃, hm₃, hcod₃, -,
      hw₃₁, hw₃'₁, hsw⟩ :=
    GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
      k f L (π ≫ p₁) hn₂ (π ⁻¹ᵁ D₁) ((π ∣_ D₁) ≫ τ₁) hτ₂f V₂ ι₂ hτι₂' w₂ hw₂ hw₂₁
  haveI := hP₃; haveI := hπ₃; haveI := hV₃; haveI := hι₃o
  haveI hp₃ : IsProper (π₃ ≫ π ≫ p₁) := inferInstance

  obtain ⟨hu, ha⟩ :=
    GoodReductionJacobian.PartialAction.unitActs_and_assoc_of_compatible_of_maximal
      k f L (π₃ ≫ π ≫ p₁) V₃ ι₃ hι₃ a₃ hc₃ hm₃

  obtain ⟨P₀, hdimW, hst, hP₀, he⟩ :=
    GoodReductionJacobian.PartialAction.exists_stable_defined_one_of_closure_image_eq_closure_singleton
      k f L (π₃ ≫ π ≫ p₁) a₃ hu ha hcod₃ w₃ w₃' hw₃₁ hw₃'₁ hsw

  haveI : Nonempty G := ⟨(L.one (𝟙 _)).1.base (IsLocalRing.closedPoint k)⟩
  have hdimG : topologicalKrullDim G = g := topologicalKrullDim_eq f g
  rw [hdim₃, hdimG] at hdimW
  exact ⟨P₃, π₃ ≫ π ≫ p₁, V₃, ι₃, hι₃, a₃, closure {w₃'}, P₀, hp₃, hP₃, hn₃, hV₃, hι₃o, hc₃, hm₃,
    hcod₃, isClosed_closure, hdimW, hst, hP₀, he⟩

end Assembly

end GoodReductionJacobian.PartialAction.GoodModel
w03_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.GoodReductionJacobian.PartialAction.GoodModel"
w03_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.GoodReductionJacobian.PartialAction"
w03_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.GoodReductionJacobian"

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f] (hG : ¬ IsProper f) :
    ∃ (V : G.Opens) (_ : Nonempty (V : Scheme.{u})) (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k))
      (_ : IsSeparated p) (_ : LocallyOfFiniteType p) (_ : IsIntegral P)
      (ι : (V : Scheme.{u}) ⟶ P) (_ : IsOpenImmersion ι) (hι : ι ≫ p = V.ι ≫ f)
      (a : PartialAction k f p), a.Compatible L V ι hι ∧ a.UnitActs L ∧ a.Assoc L ∧
      ∃ (W : Set ↥P), IsClosed W ∧ a.Stable W ∧ topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞) ∧
        ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
          P₀.1 (IsLocalRing.closedPoint k) ∈ W ∧ a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by
  obtain ⟨P, p, V, ι, hι, a, W, P₀, hp, hP, -, hV, hιo, hc, hm, -, hW, hdim, hst, hP₀, he⟩ :=
    GoodReductionJacobian.PartialAction.GoodModel.exists_model k f L g hG
  haveI := hp; haveI := hV; haveI := hιo; haveI := hP
  haveI : Smooth f := SmoothOfRelativeDimension.smooth g f
  obtain ⟨hu, ha⟩ :=
    GoodReductionJacobian.PartialAction.unitActs_and_assoc_of_compatible_of_maximal
      k f L p V ι hι a hc hm
  exact ⟨V, hV, P, p, inferInstance, inferInstance, hP, ι, hιo, hι, a, hc, hu, ha, W, hW, hst, hdim,
    P₀, hP₀, he⟩
end S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
