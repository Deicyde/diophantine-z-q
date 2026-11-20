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
  Source file    : P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.lean
  Source sha256  : 48b4b9cd8460db613ded84533366c347e09d025aab347ccf1f5e18a30bf68902
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 7 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`; `set_option synthInstance.maxHeartbeats 1600000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R2×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
r2nos_namespace_dual
r2nos_erase_attr "instance" "instTopologicallyFGOfFiniteType"
r2nos_erase_attr "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.PartialMap.compHom_hom Scheme.PartialMap.toPartialMap_toRationalMap_restrict Scheme.PartialMap IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.PartialMap.restrict_hom Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated UniversallyClosed QuasiCompact LocallyOfFiniteType Spec IsIntegral Scheme Smooth Scheme.PartialMap.isOver_iff isReduced_of_isReduced_stalk Scheme.RationalMap IsOpenImmersion isIntegral_iff_irreducibleSpace_and_isReduced UniversallyClosed.eq_valuativeCriterion Scheme.RationalMap.toRationalMap_toPartialMap IsReduced IsSeparated Scheme.homOfLE_ι ValuativeCriterion.Existence ValuativeCriterion Scheme.ΓSpecIso Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk Smooth.isDomain_and_isIntegrallyClosed_stalk"
namespace WeilExtField
r2nos_namespace_dual
namespace EXT
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

scoped instance isDomain_sections_spec (k : Type u) [Field k] :
    IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
  MulEquiv.isDomain k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

scoped instance isIntegrallyClosed_sections_spec (k : Type u) [Field k] :
    IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
  IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm

theorem isReduced_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] : IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk g x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

theorem valuationRing_stalk_of_ringKrullDim_le_one (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) ≤ 1) : ValuationRing (X.presheaf.stalk x) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨-, hic⟩ := AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk g x
  haveI : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr hx
  have key := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 4 2
  exact key.mp ⟨hic, fun P hP hP' => IsLocalRing.eq_maximalIdeal (hP'.isMaximal_of_ne_bot hP)⟩

theorem main
    {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [IsSeparated g] [QuasiCompact g] [IrreducibleSpace X]
    {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k fA)
    {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u] [Nonempty U]
    (φ : U ⟶ A) (hφ : φ ≫ fA = u ≫ g) :
    ∃ ψ : X ⟶ A, ψ ≫ fA = g ∧ u ≫ ψ = φ := by
  classical
  obtain ⟨L⟩ := hA.hasGroupLaw
  haveI : IsProper fA := hA.proper

  haveI : IsReduced X := isReduced_of_smooth k g
  haveI : IsIntegral X := (isIntegral_iff_irreducibleSpace_and_isReduced X).mpr ⟨‹_›, ‹_›⟩
  haveI : A.IsSeparated := ⟨by rw [← terminal.comp_from fA]; infer_instance⟩

  let U₀ : X.Opens := u.opensRange
  have hU₀ne : (U₀ : Set X).Nonempty := ⟨u.base (Classical.arbitrary U), ⟨_, rfl⟩⟩
  have hU₀d : Dense (U₀ : Set X) := U₀.2.dense hU₀ne
  let e := u.isoOpensRange
  let φ₀ : (U₀ : Scheme.{u}) ⟶ A := e.inv ≫ φ
  have hι : e.hom ≫ U₀.ι = u := u.isoOpensRange_hom_ι
  have hι' : e.inv ≫ u = U₀.ι := u.isoOpensRange_inv_comp
  have hφ₀ : φ₀ ≫ fA = U₀.ι ≫ g := by
    show (e.inv ≫ φ) ≫ fA = U₀.ι ≫ g
    rw [Category.assoc, hφ, ← Category.assoc, hι']
  let pm : X.PartialMap A := ⟨U₀, hU₀d, φ₀⟩
  let r := pm.toRationalMap

  letI : X.Over (Spec (CommRingCat.of k)) := ⟨g⟩
  letI : A.Over (Spec (CommRingCat.of k)) := ⟨fA⟩
  have hpm : pm.IsOver (Spec (CommRingCat.of k)) := by
    rw [Scheme.PartialMap.isOver_iff, Scheme.PartialMap.compHom_hom]
    exact hφ₀
  haveI hr : r.IsOver (Spec (CommRingCat.of k)) := ⟨⟨pm, hpm, rfl⟩⟩
  let w := r.toPartialMap
  have hwover : w.IsOver (Spec (CommRingCat.of k)) :=
    Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated.mp
      (by rw [Scheme.RationalMap.toRationalMap_toPartialMap]; exact hr)
  have hw : w.hom ≫ fA = r.domain.ι ≫ g := by
    have h := Scheme.PartialMap.isOver_iff.mp hwover
    rwa [Scheme.PartialMap.compHom_hom] at h

  have hexist : ValuativeCriterion.Existence fA := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) fA := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  have hV1 : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ r.domain := fun x hx =>
    Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk g fA hexist pm hφ₀ x
      (valuationRing_stalk_of_ringKrullDim_le_one k g x hx)

  obtain ⟨W, d, hΔ, hrec⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
      k L g r.domain hV1 ⟨w.hom, hw⟩

  obtain ⟨ψ, hψ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension_of_dense
      k L g r.domain r.dense_domain ⟨w.hom, hw⟩ W d ⟨hΔ, hrec⟩
  refine ⟨ψ.1, ψ.2, ?_⟩

  have hUV : U₀ ≤ r.domain := pm.le_domain_toRationalMap
  have hres : X.homOfLE hUV ≫ w.hom = φ₀ := by
    have h := Scheme.PartialMap.toPartialMap_toRationalMap_restrict pm
    rwa [Scheme.PartialMap.restrict_hom] at h
  have hψ' : r.domain.ι ≫ ψ.1 = w.hom := hψ
  calc u ≫ ψ.1 = e.hom ≫ U₀.ι ≫ ψ.1 := by rw [← Category.assoc, hι]
    _ = e.hom ≫ (X.homOfLE hUV ≫ r.domain.ι) ≫ ψ.1 := by rw [Scheme.homOfLE_ι]
    _ = e.hom ≫ X.homOfLE hUV ≫ w.hom := by rw [Category.assoc, hψ']
    _ = e.hom ≫ φ₀ := by rw [hres]
    _ = φ := e.hom_inv_id_assoc φ

end AlgebraicGeometry.WeilExtField.EXT
w03_reactivate "P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField.EXT"
w03_reactivate "P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField"
w03_reactivate "P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry"

end
w03_reactivate "P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField.EXT"

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [IsSeparated g] [QuasiCompact g] [IrreducibleSpace X]
    {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k fA)
    {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u] [Nonempty U]
    (φ : U ⟶ A) (hφ : φ ≫ fA = u ≫ g) :
    ∃ ψ : X ⟶ A, ψ ≫ fA = g ∧ u ≫ ψ = φ :=
  AlgebraicGeometry.WeilExtField.EXT.main g hA u φ hφ
end S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
