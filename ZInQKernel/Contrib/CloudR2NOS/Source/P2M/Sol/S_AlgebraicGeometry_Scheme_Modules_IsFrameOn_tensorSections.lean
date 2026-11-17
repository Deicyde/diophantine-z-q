/-
NEW EDITION CANDIDATE 006 (H5 lane4 a940f2af, 2026-11-17, lead request 09:41Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.lean
  Source sha256  : 8dcfeaaff7682beb271aa299645845f0e8008d2881c894b2dfd498ad3340e50b
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 10 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
r2nos_namespace_dual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TensorProduct TopologicalSpace"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Opens.ι_image_top Scheme.Modules.map_smul Scheme.Opens.opensRange_ι Scheme.Modules.tensorSections Scheme.Modules.IsFrameOn"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Hom Γ Hom.image_preimage_eq_opensRange_inf Modules Opens Opens.ι_image_top grothendieckTopology Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules Modules.tensorSections Modules.map_homOfLE_tensorSections Modules.IsFrameOn"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "hom_ext toPresheaf pushforward presheaf Hom restrict map_smul tensor tensorSectionsHom tensorSections map_homOfLE_tensorSections IsFrameOn"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace FrameTensor
r2nos_namespace_dual

variable {X : Scheme.{u}}

lemma bijective_smul_tmul {R : Type*} [CommRing R] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (a : A) (b : B)
    (ha : Function.Bijective fun r : R => r • a) (hb : Function.Bijective fun r : R => r • b) :
    Function.Bijective fun r : R => r • (a ⊗ₜ[R] b) := by
  let eA : R ≃ₗ[R] A := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R A a) ha
  let eB : R ≃ₗ[R] B := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B b) hb
  let e : R ≃ₗ[R] A ⊗[R] B := (TensorProduct.lid R R).symm ≪≫ₗ TensorProduct.congr eA eB
  have he : (fun r : R => r • (a ⊗ₜ[R] b)) = e := by
    funext r
    change r • (a ⊗ₜ[R] b) = TensorProduct.congr eA eB ((TensorProduct.lid R R).symm r)
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul, LinearEquiv.ofBijective_apply,
      LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply,
      one_smul, TensorProduct.tmul_smul]
  rw [he]
  exact e.bijective

section locbij

variable (L M : X.Modules)

def tsApp (W : X.Opens) (z : (L.val ⊗ M.val).obj (op W)) : Γ(L ⊗ M, W) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op W) :)) (β := fun _ => Γ(L ⊗ M, W))
    ((tensorSectionsHom L M).app (op W)).hom z

variable {L M}

lemma tensorSections_eq_tsApp {W : X.Opens} (s : Γ(L, W)) (t : Γ(M, W)) :
    Modules.tensorSections s t = tsApp L M W ((s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)] (t : M.val.obj (op W))) :=
  rfl

lemma tsApp_smul {W : X.Opens} (g : Γ(X, W)) (z : (L.val ⊗ M.val).obj (op W)) :
    tsApp L M W (g • z) = g • tsApp L M W z := by
  exact ((tensorSectionsHom L M).app (op W)).hom.map_smul g z

lemma tsApp_add {W : X.Opens} (z z' : (L.val ⊗ M.val).obj (op W)) :
    tsApp L M W (z + z') = tsApp L M W z + tsApp L M W z' := by
  exact ((tensorSectionsHom L M).app (op W)).hom.map_add z z'

lemma map_tsApp {W W' : X.Opens} (i : W' ⟶ W) (z : (L.val ⊗ M.val).obj (op W)) :
    (L ⊗ M).presheaf.map i.op (tsApp L M W z) = tsApp L M W' ((L.val ⊗ M.val).map i.op z) :=
  (PresheafOfModules.naturality_apply (tensorSectionsHom L M) i.op z).symm

lemma map_smul_tmul {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) (s : Γ(L, W)) (t : Γ(M, W)) :
    (L.val ⊗ M.val).map i.op (g • ((s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)] (t : M.val.obj (op W)))) =
      X.presheaf.map i.op g • ((L.presheaf.map i.op s : L.val.obj (op W')) ⊗ₜ[Γ(X, W')]
        (M.presheaf.map i.op t : M.val.obj (op W'))) := by
  erw [PresheafOfModules.map_smul, PresheafOfModules.Monoidal.tensorObj_map_tmul]
  rfl

variable (L M) in
lemma W_tensorSectionsHom :
    (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) := by
  dsimp only [tensorSectionsHom]
  rw [Functor.map_comp]
  apply MorphismProperty.comp_mem
  · erw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact GrothendieckTopology.W_toSheafify _ _
  · exact MorphismProperty.of_isIso _ _

scoped instance isLocallySurjective_tensorSectionsHom : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) :=
  (((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).1 (W_tensorSectionsHom L M)).2

scoped instance isLocallyInjective_tensorSectionsHom : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) :=
  (((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).1 (W_tensorSectionsHom L M)).1

lemma exists_local_preimage {W : X.Opens} (y : Γ(L ⊗ M, W)) {x : X} (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ⟶ W), x ∈ W' ∧ ∃ z : (L.val ⊗ M.val).obj (op W'),
      tsApp L M W' z = (L ⊗ M).presheaf.map i.op y := by
  have h := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) y
  obtain ⟨W', i, ⟨z, hz⟩, hxW'⟩ := h x hx
  exact ⟨W', i, hxW', z, hz⟩

lemma exists_local_eq {W : X.Opens} (z₁ z₂ : (L.val ⊗ M.val).obj (op W))
    (h : tsApp L M W z₁ = tsApp L M W z₂) {x : X} (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ⟶ W), x ∈ W' ∧ (L.val ⊗ M.val).map i.op z₁ = (L.val ⊗ M.val).map i.op z₂ := by
  have hm := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) z₁ z₂ h
  obtain ⟨W', i, hi, hxW'⟩ := hm x hx
  exact ⟨W', i, hxW', hi⟩

end locbij

section restrict

variable (W : X.Opens)

def restrictRingCatSheafHom : (W : Scheme.{u}).ringCatSheaf ⟶
    (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (W : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

def restrictFunctor' : X.Modules ⥤ (W : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom W)

lemma image_le (W' : (W : Scheme.{u}).Opens) : W.ι ''ᵁ W' ≤ W :=
  (W.ι.image_le_opensRange W').trans_eq W.opensRange_ι

variable {W} in
lemma image_preimage_of_le {W₂ : X.Opens} (h : W₂ ≤ W) : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) = W₂ := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

abbrev secX (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) : Γ(X, W.ι ''ᵁ W') := a

end restrict

section smulHom

variable (N : X.Modules) (W : X.Opens) (τ : Γ(N, W))

def smulSectionHom : SheafOfModules.unit ((W : X.Opens) : Scheme.{u}).ringCatSheaf ⟶
    (restrictFunctor' W).obj N :=
  ⟨{ app := fun W' => ModuleCat.ofHom
      { toFun := fun a =>
          (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ : Γ(N, W.ι ''ᵁ W'.unop))
        map_add' := fun a b => add_smul (secX W W'.unop a) (secX W W'.unop b) _
        map_smul' := fun r a => mul_smul (secX W W'.unop r) (secX W W'.unop a) _ }
     naturality := fun {W' W''} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro a
       show secX W W''.unop (X.presheaf.map (W.ι.opensFunctor.map i.unop).op (secX W W'.unop a)) •
           N.presheaf.map (homOfLE (image_le W W''.unop)).op τ =
         N.presheaf.map (W.ι.opensFunctor.map i.unop).op
           (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ)
       rw [Scheme.Modules.map_smul]
       congr 1
       change _ = (N.presheaf.map _ ≫ N.presheaf.map _) τ
       rw [← N.presheaf.map_comp]
       rfl }⟩

lemma smulSectionHom_app_apply (W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ) (a : Γ(W, W'.unop)) :
    (smulSectionHom N W τ).val.app W' a =
      secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ := rfl

variable {N W τ}

lemma bijective_smul_map_iff_of_eq {A B : X.Opens} (q : A = B) (τ : Γ(N, B)) :
    (Function.Bijective fun a : Γ(X, A) => a • N.presheaf.map (homOfLE q.le).op τ) ↔
      Function.Bijective fun g : Γ(X, B) => g • τ := by
  subst q
  have e : N.presheaf.map (homOfLE (le_refl A)).op τ = τ := by
    rw [show (homOfLE (le_refl A) : A ⟶ A) = 𝟙 A from rfl, op_id, N.presheaf.map_id]
    rfl
  simp only [e]

lemma bijective_smul_of_isIso (h : IsIso (smulSectionHom N W τ)) :
    Function.Bijective fun g : Γ(X, W) => g • τ := by
  let e := asIso (smulSectionHom N W τ)
  have hb : Function.Bijective (e.hom.val.app (op ⊤)).hom := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.inv.val.app (op ⊤)).hom, fun a => ?_, fun m => ?_⟩
    · exact congr($(e.hom_inv_id).val.app (op ⊤) |>.hom a)
    · exact congr($(e.inv_hom_id).val.app (op ⊤) |>.hom m)
  have hb' : Function.Bijective fun a : Γ(X, W.ι ''ᵁ ⊤) =>
      a • N.presheaf.map (homOfLE (Scheme.Opens.ι_image_top W).le).op τ := hb
  exact (bijective_smul_map_iff_of_eq (Scheme.Opens.ι_image_top W) τ).1 hb'

end smulHom

section main

variable {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)} {t : Γ(M, U)}

lemma bijective_smul_tmul_res (hs : IsFrameOn s V) (ht : IsFrameOn t V) {W : X.Opens}
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) =>
      g • ((L.presheaf.map (homOfLE hWU).op s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)]
        (M.presheaf.map (homOfLE hWU).op t : M.val.obj (op W))) :=
  bijective_smul_tmul (R := Γ(X, W)) _ _ (hs hWU hWV) (ht hWU hWV)

variable (W : X.Opens) (hWU : W ≤ U)

abbrev resL (W' : X.Opens) (h : W' ≤ W) : Γ(L, W') := L.presheaf.map (homOfLE (h.trans hWU)).op s

abbrev resM (W' : X.Opens) (h : W' ≤ W) : Γ(M, W') := M.presheaf.map (homOfLE (h.trans hWU)).op t

abbrev τW : Γ(L ⊗ M, W) :=
  Modules.tensorSections (L.presheaf.map (homOfLE hWU).op s) (M.presheaf.map (homOfLE hWU).op t)

lemma map_τW (W' : X.Opens) (h : W' ≤ W) :
    (L ⊗ M).presheaf.map (homOfLE h).op (τW (s := s) (t := t) W hWU) =
      tsApp L M W' ((resL (s := s) W hWU W' h : L.val.obj (op W')) ⊗ₜ[Γ(X, W')]
        (resM (t := t) W hWU W' h : M.val.obj (op W'))) := by
  dsimp only [τW]
  rw [map_homOfLE_tensorSections, tensorSections_eq_tsApp]
  congr 2
  · change (L.presheaf.map _ ≫ L.presheaf.map _) s = _
    rw [← L.presheaf.map_comp]
    rfl
  · change (M.presheaf.map _ ≫ M.presheaf.map _) t = _
    rw [← M.presheaf.map_comp]
    rfl

theorem isIso_smulSectionHom (hs : IsFrameOn s V) (ht : IsFrameOn t V) (hWV : W ≤ V) :
    IsIso (smulSectionHom (L ⊗ M) W (τW (s := s) (t := t) W hWU)) := by
  set ψ := smulSectionHom (L ⊗ M) W (τW (s := s) (t := t) W hWU)
  let J := Opens.grothendieckTopology ((W : X.Opens) : Scheme.{u})

  have pre_le : ∀ (W' : (W : Scheme.{u}).Opens) (W₂ : X.Opens), W₂ ≤ W.ι ''ᵁ W' → W.ι ⁻¹ᵁ W₂ ≤ W' := by
    intro W' W₂ h₂ w hw
    obtain ⟨w', hw', hww'⟩ := h₂ hw
    rwa [← W.ι.isOpenEmbedding.injective hww']
  have hsurj : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    rintro W' y
    refine fun x hx => ?_
    have hx' : W.ι.base x ∈ W.ι ''ᵁ W' := ⟨x, hx, rfl⟩
    obtain ⟨W₂, i₂, hxW₂, z, hz⟩ := exists_local_preimage (L := L) (M := M) y hx'
    have h₂W : W₂ ≤ W := i₂.le.trans (image_le W W')
    obtain ⟨g, hg⟩ := (bijective_smul_tmul_res hs ht (h₂W.trans hWU) (h₂W.trans hWV)).2 z
    dsimp only at hg
    have e₃ : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) ≤ W₂ := (image_preimage_of_le h₂W).le
    refine ⟨W.ι ⁻¹ᵁ W₂, homOfLE (pre_le W' W₂ i₂.le), ⟨X.presheaf.map (homOfLE e₃).op g, ?_⟩, hxW₂⟩

    have key : g • (L ⊗ M).presheaf.map (homOfLE h₂W).op (τW (s := s) (t := t) W hWU) =
        (L ⊗ M).presheaf.map i₂.op y := by
      rw [map_τW, ← tsApp_smul]
      exact (congrArg (tsApp L M W₂) hg).trans hz

    have key' := congrArg ((L ⊗ M).presheaf.map (homOfLE e₃).op) key
    rw [Scheme.Modules.map_smul] at key'
    change secX W _ (X.presheaf.map (homOfLE e₃).op g) •
        (L ⊗ M).presheaf.map (homOfLE (image_le W _)).op (τW (s := s) (t := t) W hWU) =
      (L ⊗ M).presheaf.map (W.ι.opensFunctor.map (homOfLE (pre_le W' W₂ i₂.le))).op y
    convert key' using 2
    · change _ = ((L ⊗ M).presheaf.map _ ≫ (L ⊗ M).presheaf.map _) _
      rw [← (L ⊗ M).presheaf.map_comp]
      rfl
    · change _ = ((L ⊗ M).presheaf.map _ ≫ (L ⊗ M).presheaf.map _) _
      rw [← (L ⊗ M).presheaf.map_comp]
      rfl
  have hinj : Presheaf.IsLocallyInjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    intro W' a b hab
    refine fun x hx => ?_

    have hab' : secX W W'.unop a • (L ⊗ M).presheaf.map (homOfLE (image_le W W'.unop)).op
          (τW (s := s) (t := t) W hWU) =
        secX W W'.unop b • (L ⊗ M).presheaf.map (homOfLE (image_le W W'.unop)).op
          (τW (s := s) (t := t) W hWU) := hab
    rw [map_τW, ← tsApp_smul, ← tsApp_smul] at hab'
    have hx' : W.ι.base x ∈ W.ι ''ᵁ W'.unop := ⟨x, hx, rfl⟩
    obtain ⟨W₂, i₂, hxW₂, h₂⟩ := exists_local_eq _ _ hab' hx'
    have h₂W : W₂ ≤ W := i₂.le.trans (image_le W W'.unop)
    erw [map_smul_tmul, map_smul_tmul] at h₂
    have h₃ : X.presheaf.map i₂.op (secX W W'.unop a) = X.presheaf.map i₂.op (secX W W'.unop b) := by
      apply (bijective_smul_tmul_res hs ht (h₂W.trans hWU) (h₂W.trans hWV)).1
      convert h₂ using 2 <;>
      · congr 1
        all_goals first
          | (change _ = (L.presheaf.map _ ≫ L.presheaf.map _) s
             rw [← L.presheaf.map_comp]; rfl)
          | (change _ = (M.presheaf.map _ ≫ M.presheaf.map _) t
             rw [← M.presheaf.map_comp]; rfl)
    have e₃ : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) ≤ W₂ := (image_preimage_of_le h₂W).le
    refine ⟨W.ι ⁻¹ᵁ W₂, homOfLE (pre_le W'.unop W₂ i₂.le), ?_, hxW₂⟩
    have h₄ := congrArg (X.presheaf.map (homOfLE e₃).op) h₃
    change (X.presheaf.map _ ≫ X.presheaf.map _) a = (X.presheaf.map _ ≫ X.presheaf.map _) b at h₄
    rw [← X.presheaf.map_comp] at h₄
    exact h₄
  have h₁ : IsIso ((SheafOfModules.toSheaf _).map ψ) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj, hsurj⟩
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    change IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf _).map ψ))
    infer_instance
  have := (SheafOfModules.fullyFaithfulForget
    (((W : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ)
    (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

end main

theorem isFrameOn_tensorSections {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : IsFrameOn s V) (ht : IsFrameOn t V) : IsFrameOn (Modules.tensorSections s t) V := by
  intro W hWU hWV
  have h := bijective_smul_of_isIso (isIso_smulSectionHom W hWU hs ht hWV)
  simp only [Modules.map_homOfLE_tensorSections]
  exact h

end FrameTensor
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules.FrameTensor"

end AlgebraicGeometry.Scheme.Modules
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules.FrameTensor P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules.FrameTensor P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules.FrameTensor P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry"

end
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules.FrameTensor P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules"

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.AlgebraicGeometry.Scheme.Modules" in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules} {U V : X.Opens}
    {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V)
    (ht : AlgebraicGeometry.Scheme.Modules.IsFrameOn t V) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn (AlgebraicGeometry.Scheme.Modules.tensorSections s t) V :=
  FrameTensor.isFrameOn_tensorSections hs ht
end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
