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
  Source file    : P2M/Sol/S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated.lean
  Source sha256  : c7bae0c39c6bdeac24542071c77da126b5c7b8ff672eca7b568b57033ad6596f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
r2nos_erase_attr "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated.AlgebraicGeometry TopologicalSpace"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsProper morphismRestrict_ι Scheme.Hom QuasiCompact LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Scheme IsOpenImmersion IsSeparated Scheme.homOfLE_ι_assoc Scheme.Hom.isoImage_hom_ι Scheme.Hom.isoOpensRange_hom_ι exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral"
namespace B1aReduce
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    [IsIso (g ∣_ U)] (x : X) (hx : g.base x ∈ U) : IsIso (g.stalkMap x) := by
  haveI : IsOpenImmersion ((g ⁻¹ᵁ U).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  obtain ⟨x', rfl⟩ : ∃ x' : ↥((g ⁻¹ᵁ U : X.Opens) : Scheme.{u}), (g ⁻¹ᵁ U).ι x' = x :=
    ⟨⟨x, hx⟩, rfl⟩
  have h := Scheme.Hom.stalkMap_comp (g ⁻¹ᵁ U).ι g x'
  haveI i1 : IsIso (((g ⁻¹ᵁ U).ι ≫ g).stalkMap x') := inferInstance
  haveI i2 : IsIso ((g ⁻¹ᵁ U).ι.stalkMap x') := inferInstance
  rw [h] at i1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ i2 i1

end AlgebraicGeometry.B1aReduce

open AlgebraicGeometry.B1aReduce in
r2nos_open_dual "AlgebraicGeometry.B1aReduce" in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k)) (D : P.Opens)
      (τ : (D : Scheme.{u}) ⟶ X) (V : X.Opens) (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u})),
      IsProper p ∧ IsIntegral P ∧ (∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) ∧
      IsProper τ ∧ τ ≫ f = D.ι ≫ p ∧
      Nonempty (V : Scheme.{u}) ∧ IsOpenImmersion ι ∧ ι ≫ τ = V.ι := by

  obtain ⟨X', Pt, π, j, q, hπ, -, hj, hq, hjq, hX', hPt, U, hU, hiso⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral f
  haveI := hπ; haveI := hj; haveI := hq; haveI := hX'; haveI := hPt; haveI := hiso

  obtain ⟨P, ν, hPint, hPn, hνfin, -, -, hνiso⟩ :=
    AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral k q
  haveI := hPint; haveI := hνfin

  let U₀ : Pt.Opens := j.opensRange
  let D : P.Opens := ν ⁻¹ᵁ U₀
  let τ : (D : Scheme.{u}) ⟶ X := (ν ∣_ U₀) ≫ j.isoOpensRange.inv ≫ π

  let U₁ : Pt.Opens := j ''ᵁ (π ⁻¹ᵁ U)
  have hU₁ : ∀ z ∈ U₁, IsIntegrallyClosed (Pt.presheaf.stalk z) := by
    rintro _ ⟨y, hy, rfl⟩
    haveI : IsIso (π.stalkMap y) := isIso_stalkMap_of_isIso_morphismRestrict π U y hy
    haveI : IsIntegrallyClosed (X'.presheaf.stalk y) := by
      haveI := hX (π.base y)
      exact IsIntegrallyClosed.of_equiv (asIso (π.stalkMap y)).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv (asIso (j.stalkMap y)).symm.commRingCatIsoToRingEquiv
  haveI hνU₁ : IsIso (ν ∣_ U₁) := hνiso U₁ hU₁
  have hle : ν ⁻¹ᵁ U₁ ≤ D := by
    intro z hz
    show ν.base z ∈ U₀
    obtain ⟨y, -, hy⟩ := hz
    exact ⟨y, hy⟩

  let ι : (U : Scheme.{u}) ⟶ (D : Scheme.{u}) :=
    inv (π ∣_ U) ≫ (j.isoImage (π ⁻¹ᵁ U)).hom ≫ inv (ν ∣_ U₁) ≫ P.homOfLE hle
  refine ⟨P, ν ≫ q, D, τ, U, ι, inferInstance, hPint, hPn, inferInstance, ?_, ?_, inferInstance, ?_⟩
  ·
    simp only [τ, Category.assoc]
    rw [← hjq, j.isoOpensRange_inv_comp_assoc, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  ·
    have : (U : Set X).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hU (TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_bot.symm))
    obtain ⟨x, hx⟩ := this
    exact ⟨⟨x, hx⟩⟩
  ·
    rw [← cancel_epi (π ∣_ U)]
    have hm : (j.isoImage (π ⁻¹ᵁ U)).hom ≫ inv (ν ∣_ U₁) ≫ P.homOfLE hle ≫ (ν ∣_ U₀) =
        (π ⁻¹ᵁ U).ι ≫ j.isoOpensRange.hom := by
      rw [← cancel_mono U₀.ι]
      simp only [Category.assoc, morphismRestrict_ι]
      rw [Scheme.homOfLE_ι_assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
        Scheme.Hom.isoImage_hom_ι]
      simp only [U₀, Scheme.Hom.isoOpensRange_hom_ι]
    simp only [ι, τ, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc (j.isoImage _).hom, ← Category.assoc ((j.isoImage _).hom ≫ _),
      ← Category.assoc (((j.isoImage _).hom ≫ _) ≫ _)]
    simp only [Category.assoc] at hm ⊢
    rw [reassoc_of% hm, Iso.hom_inv_id_assoc, morphismRestrict_ι]
end S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
