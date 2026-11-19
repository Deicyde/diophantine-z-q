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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id.lean
  Source sha256  : 75776fe3d51c80f164646a107455255bfe3731d8012894b988f344a51ec4ce1a
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
r2nos_erase_attr "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.Hom.finrank_comp_left_of_isIso SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsClosedImmersion.of_comp Scheme.Hom Scheme.IdealSheafData.comapIso Scheme.IdealSheafData.comapIso_hom_fst_assoc IsFinite Scheme Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Flat IsClosedImmersion IsSeparated LocallyOfFinitePresentation Scheme.IdealSheafData graphOver graphOver_fst RelEffCartierDiv RelEffCartierDiv.exists_I_eq_prodKerGraph Scheme.IdealSheafData.comap_mul"
namespace SectionPowDivisor
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

variable {X T : Scheme.{u}}

lemma comap_pow {Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (J ^ n).comap f = J.comap f ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

lemma ker_graphOver_eq_comap {p : X ⟶ T} [IsSeparated p] (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) :
    (graphOver p σ hσ).ker = σ.ker.comap (pullback.fst p (𝟙 T)) := by
  haveI : IsClosedImmersion (σ ≫ p) := by rw [hσ]; infer_instance
  haveI : IsClosedImmersion σ := IsClosedImmersion.of_comp σ p
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h : pullback.fst (pullback.fst p (𝟙 T)) σ =
      pullback.snd (pullback.fst p (𝟙 T)) σ ≫ graphOver p σ hσ := by
    rw [← cancel_mono (pullback.fst p (𝟙 T)), Category.assoc, graphOver_fst]
    exact pullback.condition
  rw [h, Scheme.Hom.ker_comp_of_isIso]

lemma transport {P : Scheme.{u}} (e : P ⟶ X) [IsIso e] (p : X ⟶ T) (J : X.IdealSheafData) (r : ℕ)
    (hfin : IsFinite ((J.comap e).subschemeι ≫ e ≫ p))
    (hflat : Flat ((J.comap e).subschemeι ≫ e ≫ p))
    (hlfp : LocallyOfFinitePresentation ((J.comap e).subschemeι ≫ e ≫ p))
    (hrk : ∀ t : T, ((J.comap e).subschemeι ≫ e ≫ p).finrank t = r) :
    IsFinite (J.subschemeι ≫ p) ∧ (∀ t : T, (J.subschemeι ≫ p).finrank t = r) ∧
      Flat (J.subschemeι ≫ p) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ p) := by
  obtain ⟨φ, hφiso, hφ⟩ : ∃ φ : (J.comap e).subscheme ⟶ J.subscheme,
      IsIso φ ∧ φ ≫ J.subschemeι ≫ p = (J.comap e).subschemeι ≫ e ≫ p :=
    ⟨(J.comapIso e).hom ≫ pullback.snd e J.subschemeι, inferInstance, by
      rw [Category.assoc, ← pullback.condition_assoc,
        Scheme.IdealSheafData.comapIso_hom_fst_assoc]⟩
  haveI := hφiso
  rw [← hφ] at hfin hflat hlfp hrk
  have h1 : IsFinite (J.subschemeι ≫ p) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsFinite φ _).mp hfin
  have h3 : Flat (J.subschemeι ≫ p) :=
    (MorphismProperty.cancel_left_of_respectsIso @Flat φ _).mp hflat
  have h4 : LocallyOfFinitePresentation (J.subschemeι ≫ p) :=
    (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation φ _).mp hlfp
  refine ⟨h1, fun t => ?_, h3, h4⟩
  rw [← Scheme.Hom.finrank_comp_left_of_isIso φ (J.subschemeι ≫ p)]
  exact hrk t

theorem main {p : X ⟶ T} [IsSeparated p] [SmoothOfRelativeDimension 1 p]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) (r : ℕ) :
    IsFinite ((σ.ker ^ r).subschemeι ≫ p) ∧
      (∀ t : T, ((σ.ker ^ r).subschemeι ≫ p).finrank t = r) ∧
      Flat ((σ.ker ^ r).subschemeι ≫ p) ∧
      LocallyOfFinitePresentation ((σ.ker ^ r).subschemeι ≫ p) := by
  obtain ⟨⟨I, hfin, hflat, hlfp, hrk⟩, hI⟩ :=
    RelEffCartierDiv.exists_I_eq_prodKerGraph (f := p) (g := 𝟙 T) (fun _ : Fin r => σ) (fun _ => hσ)
  have hI' : I = (σ.ker ^ r).comap (pullback.fst p (𝟙 T)) := by
    rw [comap_pow, ← ker_graphOver_eq_comap σ hσ, ← Fin.prod_const]
    exact hI
  subst hI'
  have hsnd : pullback.fst p (𝟙 T) ≫ p = pullback.snd p (𝟙 T) := by
    rw [pullback.condition, Category.comp_id]
  rw [← hsnd] at hfin hflat hlfp hrk
  exact transport (pullback.fst p (𝟙 T)) p (σ.ker ^ r) r hfin hflat hlfp hrk

end AlgebraicGeometry.SectionPowDivisor

theorem solution
    {X T : Scheme.{u}} {p : X ⟶ T} [IsSeparated p] [SmoothOfRelativeDimension 1 p]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) (r : ℕ) :
    IsFinite ((σ.ker ^ r).subschemeι ≫ p) ∧
      (∀ t : T, ((σ.ker ^ r).subschemeι ≫ p).finrank t = r) ∧
      Flat ((σ.ker ^ r).subschemeι ≫ p) ∧
      LocallyOfFinitePresentation ((σ.ker ^ r).subschemeι ≫ p) :=
  AlgebraicGeometry.SectionPowDivisor.main σ hσ r
end S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
