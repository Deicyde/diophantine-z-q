/-
NOS-CORE PROBE STAGING COPY (NOS-core probe, lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_RelPicardAbelJacobiFamily.lean
  Source sha256  : 6e36c3db2748ffa1c8bd5896b21f18f19d68a1ea29c4442f079935e4a721754c
  Retrieved      : pinned upstream https://github.com/anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2, byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 12 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-8 (lane C4): T10×1
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open CategoryTheory
r2nos_open_dual "CategoryTheory"
open CategoryTheory.Limits
r2nos_open_dual "CategoryTheory.Limits"
open MonoidalCategory
r2nos_open_dual "MonoidalCategory"
open AlgebraicGeometry
r2nos_open_dual "AlgebraicGeometry"
open AlgebraicGeometry.RelPicard
r2nos_open_dual "AlgebraicGeometry.RelPicard"
open NeronModelInfra
r2nos_open_dual "NeronModelInfra"
open GoodReductionJacobian
r2nos_open_dual "GoodReductionJacobian"

noncomputable section

namespace AlgebraicGeometry.RelPicard
r2nos_namespace_dual

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))

def toProdSpec : A ⟶ Limits.pullback a (𝟙 (Spec (CommRingCat.of k))) :=
  pullback.lift (𝟙 A) a (by simp)

@[reassoc (attr := simp)]
theorem toProdSpec_fst : toProdSpec a ≫ pullback.fst a (𝟙 _) = 𝟙 A := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fst_toProdSpec : pullback.fst a (𝟙 _) ≫ toProdSpec a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [toProdSpec, Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · simp only [toProdSpec, Category.assoc, pullback.lift_snd, Category.id_comp]
    rw [pullback.condition, Category.comp_id]

def fstPullbackToProdSpecPullbackIso (N : (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules) :
    (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj ((Scheme.Modules.pullback (toProdSpec a)).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr (fst_toProdSpec a)).app N ≪≫
    (Scheme.Modules.pullbackId _).app N

def toProdSpecPullbackFstPullbackIso (L : A.Modules) :
    (Scheme.Modules.pullback (toProdSpec a)).obj ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L) ≅ L :=
  (Scheme.Modules.pullbackComp _ _).app L ≪≫ (Scheme.Modules.pullbackCongr (toProdSpec_fst a)).app L ≪≫
    (Scheme.Modules.pullbackId _).app L

variable {a}

theorem baseChangeSnd_eq_mapOnProdOver {T' : Scheme.{u}} {h : T' ⟶ Spec (CommRingCat.of k)}
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) : baseChangeSnd a t = mapOnProdOver a t.1 t.2 := rfl

theorem IsAlgEquivZero.tensorUnit (a : A ⟶ Spec (CommRingCat.of k)) : IsAlgEquivZero a (𝟙_ A.Modules) := by
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf, Scheme.Modules.isInvertible_unit _,
    ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm

theorem IsAlgEquivZero.of_fst_pullback_iso {L : A.Modules}
    {N : (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ N)
    (hN : IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj N)) : IsAlgEquivZero a L :=
  IsAlgEquivZero.of_iso ((Scheme.Modules.pullback (toProdSpec a)).mapIso e.symm ≪≫ toProdSpecPullbackFstPullbackIso a L) hN

theorem RelEffCartierDiv.ofPoint_congr {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}}
    {g : T ⟶ S} {x y : T ⟶ 𝒞} (h : x = y) (hx : x ≫ f = g) (hy : y ≫ f = g) :
    RelEffCartierDiv.ofPoint f x hx = RelEffCartierDiv.ofPoint f y hy := by
  subst h; rfl

theorem Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso {X : Scheme.{u}}
    {I : X.IdealSheafData} (hI : I.IsInvertible) : Nonempty (I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) :=
  ⟨β_ _ _ ≪≫ (hI.isInvertible_module.dual).2.some⟩

section
variable [IsSeparated a]

abbrev pointSubBasepointModule (t ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules :=
  (RelEffCartierDiv.ofPoint a t.1 t.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint a ε.1 ε.2).idealModule

def pointsSubBasepointModule (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) → (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules
  | [] => 𝟙_ _
  | P :: Ps => pointSubBasepointModule (a := a) P ε ⊗ pointsSubBasepointModule ε Ps

@[simp] theorem pointsSubBasepointModule_nil (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    pointsSubBasepointModule (a := a) ε [] = 𝟙_ _ := rfl

@[simp] theorem pointsSubBasepointModule_cons (ε P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)) :
    pointsSubBasepointModule (a := a) ε (P :: Ps) = pointSubBasepointModule (a := a) P ε ⊗ pointsSubBasepointModule ε Ps :=
  rfl

abbrev diagDiv : RelEffCartierDiv a 1 a := RelEffCartierDiv.ofPoint a (𝟙 A) (Category.id_comp a)

omit [IsSeparated a] in
theorem comp_point_comp (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : (a ≫ ε.1) ≫ a = a := by
  rw [Category.assoc, ε.2, Category.comp_id]

abbrev constDiv (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : RelEffCartierDiv a 1 a :=
  RelEffCartierDiv.ofPoint a (a ≫ ε.1) (comp_point_comp ε)

def ajFamily (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : (Limits.pullback a a).Modules :=
  (diagDiv (a := a)).lineBundle ⊗ (constDiv (a := a) ε).idealModule

theorem isInvertible_ajFamily [SmoothOfRelativeDimension 1 a] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    Scheme.Modules.IsInvertible (ajFamily (a := a) ε) :=
  (RelEffCartierDiv.isInvertible_I _).isInvertible_invModule.tensor (RelEffCartierDiv.isInvertible_I _).isInvertible_module

end

end AlgebraicGeometry.RelPicard

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
