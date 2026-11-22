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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.lean
  Source sha256  : b21e4185cfb6446b7d9f359a8064e590d16a00e0e8202235e386207c6d81ad50
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top Scheme.Hom Spec Scheme IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.IdealSheafData RelEffCartierDiv graphOver graphOver_snd RelEffCartierDiv.ofPoint Scheme.IdealSheafData.IsInvertible prodKerGraph prodKerGraph_eq_prod prodKerGraph_zero Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor"
namespace RelPicard
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelPicard" "Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons"
namespace TensorList
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

w03_open "AlgebraicGeometry.RelPicard.Scheme AlgebraicGeometry.Scheme"

variable {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
  [IsSeparated a] [SmoothOfRelativeDimension 1 a]

noncomputable def shuffle {X : Scheme.{u}} (X₁ X₂ Y₁ Y₂ : X.Modules) :
    (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ≅ (X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂) :=
  (α_ X₁ X₂ (Y₁ ⊗ Y₂)) ≪≫
    whiskerLeftIso X₁ ((α_ X₂ Y₁ Y₂).symm ≪≫ whiskerRightIso (β_ X₂ Y₁) Y₂ ≪≫ α_ Y₁ X₂ Y₂) ≪≫
    (α_ X₁ Y₁ (X₂ ⊗ Y₂)).symm

lemma isInvertible_ker (P : Spec (CommRingCat.of k) ⟶ A) (hP : P ≫ a = 𝟙 _) :
    (graphOver a P hP).ker.IsInvertible :=
by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd a (𝟙 _)) (graphOver a P hP) (graphOver_snd a P hP)

lemma isInvertible_prodKerGraph {r : ℕ} (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    (prodKerGraph a P hP).IsInvertible := by
  induction r with
  | zero => rw [prodKerGraph_zero]; exact IdealSheafData.isInvertible_top
  | succ r ih =>
    rw [prodKerGraph_eq_prod, Fin.prod_univ_succ]
    exact (isInvertible_ker (P 0) (hP 0)).mul (ih (fun i => P i.succ) (fun i => hP i.succ))

lemma isInvertible_pow {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    (I ^ n).IsInvertible := by
  induction n with
  | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact IdealSheafData.isInvertible_top
  | succ n ih => rw [pow_succ]; exact ih.mul hI

theorem main (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) := by
  induction r with
  | zero =>
    have h1 : prodKerGraph a P hP = ⊤ := prodKerGraph_zero a P hP
    have h2 : (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ 0 = ⊤ := by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    rw [List.ofFn_zero, pointsSubBasepointModule_nil, h1, h2]
    exact Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso IdealSheafData.isInvertible_top
  | succ r ih =>

    let I₀ := (graphOver a (P 0) (hP 0)).ker
    let J := prodKerGraph a (fun i => P i.succ) (fun i => hP i.succ)
    let Iε := (RelEffCartierDiv.ofPoint a ε.1 ε.2).I
    have hprod : prodKerGraph a P hP = I₀ * J := by
      simp only [I₀, J, prodKerGraph_eq_prod]
      rw [Fin.prod_univ_succ]
    have hpow : Iε ^ (r + 1) = Iε * Iε ^ r := pow_succ' Iε r
    have hI₀ : I₀.IsInvertible := isInvertible_ker (P 0) (hP 0)
    have hJ : J.IsInvertible := isInvertible_prodKerGraph _ _
    have hIε : Iε.IsInvertible := isInvertible_ker ε.1 ε.2
    have hIεr : (Iε ^ r).IsInvertible := isInvertible_pow hIε r
    obtain ⟨e₁⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hI₀ hJ
    obtain ⟨e₂⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor hIε hIεr
    obtain ⟨e₃⟩ := ih (fun i => P i.succ) (fun i => hP i.succ)
    rw [List.ofFn_succ, pointsSubBasepointModule_cons]
    have c₁ : (prodKerGraph a P hP).invModule ≅ (I₀ * J).invModule := eqToIso (by rw [hprod])
    have c₂ : ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ (r + 1)).module ≅ (Iε * Iε ^ r).module :=
      eqToIso (by rw [show (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ (r + 1) = Iε * Iε ^ r from hpow])
    exact ⟨(c₁ ⊗ᵢ c₂) ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ shuffle _ _ _ _ ≪≫ whiskerLeftIso _ e₃⟩

end AlgebraicGeometry.RelPicard.TensorList

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) :=
  AlgebraicGeometry.RelPicard.TensorList.main ε P hP
end S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
