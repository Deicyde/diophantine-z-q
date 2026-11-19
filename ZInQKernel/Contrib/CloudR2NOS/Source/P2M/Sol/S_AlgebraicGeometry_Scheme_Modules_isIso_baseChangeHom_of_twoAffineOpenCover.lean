/-
NOS-CORE PROBE STAGING COPY (nos-core-probe-001, lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.lean
  Source sha256  : 5be5d1215ee743d722ba292c89600497c8e5698ca260f59fab6b01ab452a030b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 12 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 3200000 in`; `set_option maxHeartbeats 6400000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 14 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

/-
DEFAULT-LIMIT EDITION, 2026-11-17. The attributed base above is preserved.
The actual global-sections comparison is proved in its own declaration.
The geometric tensor equality uses a separately proved one-tensor
extensionality lemma, and bijectivity uses a separately proved actual
square-of-equivalences lemma rather than an expanded inverse function.
The presheaf-map comparison names the actual pulled-back module explicitly.
Every existing declaration statement/import/option is retained. No numeric
limit or new final IsIso/rank/model Fact is supplied. SOURCE only; parent
owns compilation and C4 owns binding. Inherited switches are disclosed.
-/

/-
DEFAULT-LIMIT CONTINUATION v2, 2026-11-17. The failed b278cd73 SOURCE and
all earlier diff/log/receipts remain separate and unchanged. Two genuine
local formulas are proved independently: the original kernel base-change
map at `1 ⊗ x`, and the original base-change morphism's unit restricted to
one open set. The large Cech square now uses these formulas, avoiding its
repeated kernel-membership construction and the two underconstrained
presheaf-map composition applications. Every existing declaration name,
statement, import and nonnumeric option is retained. No numeric limits or
new final Facts; SOURCE only, parent probes and C4 binds.
-/

/-
DEFAULT-LIMIT CONTINUATION v3, 2026-11-17. Failed 1e6bf1d6 SOURCE and
all previous editions/diffs/logs are preserved. The unit formula first
normalizes the actual identity presheaf map at the morphism level, before
applying it to a section. This fixes the ConcreteCategory/composite mismatch.
The Cech unit comparison is proved with the actual chosen equivalences as
parameters, and its bijective square is assembled by a separate pure
linear-algebra proof. The final consumer supplies every equivalence/formula
from the same existing section/kernel lemmas; no final Fact is assumed.
All existing names/statements/imports/attribution/nonnumeric options remain.
No numeric budget change or lane compilation. Parent probes; C4 binds.
-/

/-
DEFAULT-LIMIT CONTINUATION v4, 2026-11-17. Failed 9304a095 SOURCE and
all previous editions/diffs/logs are preserved. The original type-correct
unit-composition equation is evaluated on the actual section before its
identity presheaf map is simplified, so no large ill-typed composite is
rewritten at implicit transparency. Local notation expands ordinary
Functor.obj/Functor.map and ModuleCat.Hom.hom applications; projections
from notation aliases are parenthesized terms, not namespace identifiers.
This is a syntax repair of the SAME intended helper telescope, not a new
mathematical input. All declaration names, intended statements, imports,
attribution and nonnumeric options remain. No quotPrecheck switch or
numeric limit is added. SOURCE only; parent probes and C4 binds.
-/

/-
Default-limit continuation, 2026-11-17.
The section identity is derived by evaluating the original composition
equation, explicitly exposing both function applications, and applying the
actual presheaf's identity-map theorem to that section. The quotation
abbreviation uses the fully qualified commutative-ring constructor.
All declaration names, statements, imports, attribution and nonnumeric
options are retained. No new mathematical hypothesis or limit is added.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_TwoChartCech_Mumford_projective_ker_of_fibre_surjective
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover
r2nos_namespace_dual
r2nos_erase_attr "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry Opposite TopologicalSpace TensorProduct"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Surjective Scheme.Modules.pushforward Scheme.Modules.pullback tilde.adjunction Scheme.Hom moduleSpecΓFunctor Spec Spec.map isIso_fromTildeΓ_iff Scheme.Modules.mapPresheaf_app Scheme pullbackSpecIso Scheme.Modules.fromTildeΓ Flat modulesSpecToSheaf Scheme.Modules.pullbackPushforwardAdjunction tilde.functor IsAffineOpen Scheme.Modules tilde Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.Modules.baseChangeHom tilde.pullbackSpecIso Scheme.Modules.IsInvertible Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Modules.mapPresheaf_app Modules.fromTildeΓ Modules.pullbackPushforwardAdjunction Modules Opens ΓSpecIso Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.specMap Modules.baseChangeHom Modules.IsInvertible Modules.isIso_baseChangeHom_iff_of_isPullback"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom mapPresheaf_app fromTildeΓ pullbackPushforwardAdjunction map_smul baseChangeHom unit_app_app_comp_baseChangeHom_app IsInvertible isIso_fromTildeGamma_pushforward_of_locallyTrivial projective_sections_of_locallyTrivial exists_linearEquiv_sections_baseChange_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma isIso_baseChangeHom_iff_of_isPullback"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem isIso_of_isIso_moduleSpecΓFunctor_map {A : Type u} [CommRing A]
    {M N : (Spec (CommRingCat.of A)).Modules}
    (hM : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) M)) (hN : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) N))
    (f : M ⟶ N) (hf : IsIso ((moduleSpecΓFunctor (R := .of A)).map f)) : IsIso f := by

  have hnat : (tilde.functor (.of A)).map ((moduleSpecΓFunctor (R := .of A)).map f) ≫
      Scheme.Modules.fromTildeΓ (R := .of A) N = Scheme.Modules.fromTildeΓ (R := .of A) M ≫ f :=
    (tilde.adjunction (R := .of A)).counit.naturality f
  let e : M ≅ N := (@asIso _ _ _ _ _ hM).symm ≪≫ (tilde.functor (.of A)).mapIso (@asIso _ _ _ _ _ hf) ≪≫
    @asIso _ _ _ _ _ hN
  have he : e.hom = f := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, asIso_inv]
    exact (@IsIso.inv_comp_eq _ _ _ _ _ _ hM _ _).mpr hnat
  rw [← he]
  infer_instance

namespace Hom
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules.Hom" "mapPresheaf app"
end Hom
r2nos_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

lemma Hom.app_presheaf_map {X : Scheme.{u}} {F G : X.Modules} (η : F ⟶ G) {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)) :
    (η.app V).hom (F.presheaf.map i.op s) = G.presheaf.map i.op ((η.app U).hom s) := by
  have h := η.mapPresheaf.naturality i.op
  simp only [Scheme.Modules.mapPresheaf_app] at h
  simpa [CategoryTheory.comp_apply] using ConcreteCategory.congr_hom h s

section resM
variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev resM {W W' : X.Opens} (h : W' ≤ W) : Γ(M, W) → Γ(M, W') :=
  fun s => M.presheaf.map (homOfLE h).op s

variable {M}

lemma map_eq_resM {W W' : X.Opens} (i : W' ⟶ W) (s : Γ(M, W)) : M.presheaf.map i.op s = resM M i.le s := by
  rw [Subsingleton.elim i (homOfLE i.le)]

lemma resM_resM {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (s : Γ(M, W)) :
    resM M h' (resM M h s) = resM M (h'.trans h) s := by
  change (M.presheaf.map (homOfLE h).op ≫ M.presheaf.map (homOfLE h').op) s = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma resM_refl {W : X.Opens} (h : W ≤ W) (s : Γ(M, W)) : resM M h s = s := by
  change M.presheaf.map (homOfLE h).op s = s
  rw [Subsingleton.elim (homOfLE h) (𝟙 W), op_id, CategoryTheory.Functor.map_id]
  rfl

lemma presheaf_map_map_eq (M : X.Modules) {U V W : X.Opens} (a : V ⟶ U) (b : W ⟶ V) (c : W ⟶ U)
    (s : Γ(M, U)) : M.presheaf.map b.op (M.presheaf.map a.op s) = M.presheaf.map c.op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (b ≫ a) c]

end resM

private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.Module.Flat.prod_of_flat {R : Type u} [CommRing R] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) f hf
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
  have hsq : ∀ x, TensorProduct.prodRight R R Q M N (f.rTensor (M × N) x) =
      ((f.rTensor M).prodMap (f.rTensor N)) (TensorProduct.prodRight R R P M N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul p mn => simp [LinearMap.rTensor_tmul, LinearMap.prodMap_apply, TensorProduct.prodRight_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  have h := congrArg (TensorProduct.prodRight R R Q M N) hxy
  rw [hsq, hsq] at h
  have hinj : Function.Injective ((f.rTensor M).prodMap (f.rTensor N)) := h1.prodMap h2
  exact (TensorProduct.prodRight R R P M N).injective (hinj h)

r2nos_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.Module.Flat.prod_of_flat" "Module.Flat.prod_of_flat"

section bridge
variable {A : Type u} [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A']

noncomputable def restrictScalarsSelfEquiv :
    A' ≃ₗ[A'] ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A' A')) :=
  LinearEquiv.refl A' A'

scoped instance : IsScalarTower A A'
    ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A' A')) :=
  ⟨fun a a' x => by
    change (a • a') • x = ((algebraMap A A') a) • (a' • x)
    rw [Algebra.smul_def, mul_smul]⟩

noncomputable def extendScalarsAlgebraMapEquiv (N : ModuleCat.{u} A) :
    (A' ⊗[A] N) ≃ₗ[A'] (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj N :=
  TensorProduct.AlgebraTensorModule.congr (restrictScalarsSelfEquiv (A := A) A') (LinearEquiv.refl A N)

theorem extendScalarsAlgebraMapEquiv_tmul (N : ModuleCat.{u} A) (a' : A') (n : N) :
    extendScalarsAlgebraMapEquiv (A := A) A' N (a' ⊗ₜ n) =
      ((a' : ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A' A'))) ⊗ₜ[A] n :
        (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj N) := by
  rfl

end bridge

section main

w03_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))

noncomputable abbrev globalSectionsModule (F : X.Modules) : ModuleCat A :=
  ((modulesSpecToSheaf (R := .of A)).obj ((Scheme.Modules.pushforward π).obj F)).presheaf.obj (op ⊤)

noncomputable def globalSectionsEquiv (F : X.Modules) :
    letI := moduleSectionsOfHom π F ⊤
    globalSectionsModule π F ≃ₗ[A] Γ(F, ⊤) :=
  letI := moduleSectionsOfHom π F ⊤
  { toFun := fun s => (show Γ(F, ⊤) from s)
    invFun := fun s => (show globalSectionsModule π F from s)
    map_add' := fun _ _ => rfl
    map_smul' := fun a s => by
      show (show Γ(X, ⊤) from ((π.app ⊤).hom ((((Spec (CommRingCat.of A)).presheaf.map
          (homOfLE (le_top (a := ⊤))).op).hom) ((Scheme.ΓSpecIso (.of A)).inv.hom a)))) • (show Γ(F, ⊤) from s) =
        ((π.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) • (show Γ(F, ⊤) from s)
      congr 1
      have h1 : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ ⊤)) = 𝟙 _ :=
        Subsingleton.elim _ _
      have e1 : (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of A)).Opens)))).op = 𝟙 _ := by
        rw [h1, op_id, CategoryTheory.Functor.map_id]
      have e2 : π.appLE ⊤ ⊤ le_top = π.app ⊤ := Scheme.Hom.appLE_eq_app _
      rw [e2, e1]
      rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

noncomputable abbrev ΓMod (N : (Spec (CommRingCat.of A)).Modules) : ModuleCat A :=
  (moduleSpecΓFunctor (R := .of A)).obj N

variable (A' : Type u) [CommRing A'] [Algebra A A']

noncomputable abbrev φA : CommRingCat.of A ⟶ CommRingCat.of A' := CommRingCat.ofHom (algebraMap A A')

lemma specMap_eq : Scheme.TwoAffineOpenCover.specMap A A' = Spec.map (φA (A := A) A') := rfl

theorem exists_linearEquiv_tensor_ΓMod_pullback (N : (Spec (CommRingCat.of A)).Modules)
    (hN : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) N)) :
    ∃ σ : A' ⊗[A] (ΓMod N) ≃ₗ[A']
        ((moduleSpecΓFunctor (R := .of A')).obj ((pullback (Spec.map (φA (A := A) A'))).obj N)),
      ∀ m : ΓMod N, σ ((1 : A') ⊗ₜ[A] m) =
        ((((pullbackPushforwardAdjunction (Spec.map (φA (A := A) A'))).unit.app N).app ⊤).hom m :) := by
  have hiso := isIso_baseChange_sections_of_isIso_fromTildeGamma (φA (A := A) A') N hN
  let τ := @asIso _ _ _ _ _ hiso
  refine ⟨(extendScalarsAlgebraMapEquiv (A := A) A' (ΓMod N)).trans τ.toLinearEquiv, fun m => ?_⟩
  rw [LinearEquiv.trans_apply, extendScalarsAlgebraMapEquiv_tmul]
  refine Eq.trans (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply τ.hom m).symm ?_
  simp only [τ, asIso_hom, Equiv.apply_symm_apply]
  rfl

theorem exists_linearEquiv_ker_baseChange_cechDiff (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    (Function.Surjective ((𝒱.pullback π A').sectionsOf
          (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A A'))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).obj F)).cechDiff →
      Function.Surjective ((𝒱.sectionsOf π F).cechDiff.baseChange A')) ∧
    ∃ κ : LinearMap.ker ((𝒱.sectionsOf π F).cechDiff.baseChange A') ≃ₗ[A']
        LinearMap.ker ((𝒱.pullback π A').sectionsOf
          (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A A'))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).obj F)).cechDiff,
      ∀ (x : (𝒱.sectionsOf π F).M0 × (𝒱.sectionsOf π F).M1)
        (hx : (1 : A') ⊗ₜ[A] x ∈ LinearMap.ker ((𝒱.sectionsOf π F).cechDiff.baseChange A')),
        (κ ⟨(1 : A') ⊗ₜ[A] x, hx⟩).1 =
          ((((Scheme.Modules.pullbackPushforwardAdjunction
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).unit.app F).app 𝒱.U0).hom x.1,
           (((Scheme.Modules.pullbackPushforwardAdjunction
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).unit.app F).app 𝒱.U1).hom x.2) := by
  classical
  set S := 𝒱.sectionsOf π F with hS
  set fK := Limits.pullback.fst π (specMap A A') with hfK
  set FK : (Limits.pullback π (specMap A A')).Modules := (Scheme.Modules.pullback fK).obj F with hFK
  set SK := (𝒱.pullback π A').sectionsOf (Limits.pullback.snd π (specMap A A')) FK with hSK
  let η := (Scheme.Modules.pullbackPushforwardAdjunction fK).unit.app F
  letI := moduleSectionsOfHom π F 𝒱.U0
  letI := moduleSectionsOfHom π F 𝒱.U1
  letI := moduleSectionsOfHom π F (𝒱.U0 ⊓ 𝒱.U1)
  letI := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ 𝒱.U0)
  letI := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ 𝒱.U1)
  letI := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
  obtain ⟨ε0, hε0⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U0
    𝒱.isAffineOpen_U0 A'
  obtain ⟨ε1, hε1⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U1
    𝒱.isAffineOpen_U1 A'
  obtain ⟨ε01, hε01⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv (𝒱.U0 ⊓ 𝒱.U1)
    𝒱.isAffineOpen_inf A'
  let e0 : A' ⊗[A] (S.M0 × S.M1) ≃ₗ[A'] (SK.M0 × SK.M1) :=
    (TensorProduct.prodRight A A' A' S.M0 S.M1).trans (ε0.prodCongr ε1)
  let e1 : A' ⊗[A] S.M01 ≃ₗ[A'] SK.M01 := ε01
  have hr0 : ∀ s : S.M0, SK.r0 (ε0 ((1 : A') ⊗ₜ[A] s)) = ε01 ((1 : A') ⊗ₜ[A] (S.r0 s)) := by
    intro s
    rw [hε0, hε01]
    exact (Hom.app_presheaf_map η (homOfLE inf_le_left) s).symm
  have hr1 : ∀ s : S.M1, SK.r1 (ε1 ((1 : A') ⊗ₜ[A] s)) = ε01 ((1 : A') ⊗ₜ[A] (S.r1 s)) := by
    intro s
    rw [hε1, hε01]
    exact (Hom.app_presheaf_map η (homOfLE inf_le_right) s).symm
  have he0 : ∀ (s0 : S.M0) (s1 : S.M1),
      e0 ((1 : A') ⊗ₜ[A] (s0, s1)) = (ε0 ((1 : A') ⊗ₜ[A] s0), ε1 ((1 : A') ⊗ₜ[A] s1)) := by
    intro s0 s1
    simp only [e0, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
    rfl
  have hcomm : SK.cechDiff ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ S.cechDiff.baseChange A' := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul k x => ?_
    obtain ⟨s0, s1⟩ := x
    have hk : ∀ {N : Type u} [AddCommGroup N] [Module A N] (y : N),
        (k ⊗ₜ[A] y : A' ⊗[A] N) = k • ((1 : A') ⊗ₜ[A] y) := fun y => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hk, _root_.map_smul, _root_.map_smul, _root_.map_smul, _root_.map_smul]
    congr 1
    have he1 : ∀ y, e1 y = ε01 y := fun _ => rfl
    rw [he0, he1, LinearMap.baseChange_tmul, TwoChartCech.Sections.cechDiff_apply,
      TwoChartCech.Sections.cechDiff_apply]
    dsimp only
    rw [TensorProduct.tmul_sub, hr0, hr1]
    exact (map_sub ε01 _ _).symm

  have hmem : ∀ y, y ∈ LinearMap.ker (S.cechDiff.baseChange A') ↔ e0 y ∈ LinearMap.ker SK.cechDiff := by
    intro y
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have h1 : SK.cechDiff (e0 y) = e1 (S.cechDiff.baseChange A' y) :=
      congrArg (fun φ : _ →ₗ[A'] _ => φ y) hcomm
    rw [h1]
    exact ⟨fun h => by rw [h, map_zero], fun h => e1.injective (by rw [h, map_zero])⟩
  let κ₀ : LinearMap.ker (S.cechDiff.baseChange A') →ₗ[A'] LinearMap.ker SK.cechDiff :=
    (e0.toLinearMap ∘ₗ (LinearMap.ker (S.cechDiff.baseChange A')).subtype).codRestrict _
      (fun y => (hmem y.1).mp y.2)
  have hκ₀ : Function.Bijective κ₀ := by
    refine ⟨fun y z h => Subtype.ext (e0.injective (congrArg Subtype.val h)), fun z => ?_⟩
    refine ⟨⟨e0.symm z.1, (hmem _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
    exact Subtype.ext (e0.apply_symm_apply z.1)
  refine ⟨fun hs => ?_, LinearEquiv.ofBijective κ₀ hκ₀, fun x hx => ?_⟩
  · have hd : ∀ y, S.cechDiff.baseChange A' y = e1.symm (SK.cechDiff (e0 y)) := fun y => by
      have h1 : SK.cechDiff (e0 y) = e1 (S.cechDiff.baseChange A' y) :=
        congrArg (fun φ : _ →ₗ[A'] _ => φ y) hcomm
      rw [h1, LinearEquiv.symm_apply_apply]
    intro z
    obtain ⟨w, hw⟩ := hs (e1 z)
    exact ⟨e0.symm w, by rw [hd, LinearEquiv.apply_symm_apply, hw, LinearEquiv.symm_apply_apply]⟩
  obtain ⟨s0, s1⟩ := x
  rw [LinearEquiv.ofBijective_apply]
  change e0 ((1 : A') ⊗ₜ[A] (s0, s1)) = _
  rw [he0, hε0, hε1]
  rfl


theorem isIso_fromTildeΓ_pullback_pushforward (F : X.Modules)
    (hF : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) ((pushforward π).obj F))) :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of A')
      ((pullback (Spec.map (φA (A := A) A'))).obj ((pushforward π).obj F))) := by
  rw [isIso_fromTildeΓ_iff]
  let H : ModuleCat A := ΓMod ((pushforward π).obj F)
  let e1 : tilde H ≅ (pushforward π).obj F := @asIso _ _ _ _ _ hF
  let e2 : (pullback (Spec.map (φA (A := A) A'))).obj (tilde H) ≅
      tilde ((ModuleCat.extendScalars (φA (A := A) A').hom).obj H) := tilde.pullbackSpecIso (φA (A := A) A') H
  refine ⟨(ModuleCat.extendScalars (φA (A := A) A').hom).obj H, ⟨?_⟩⟩
  exact e2.symm ≪≫ (pullback (Spec.map (φA (A := A) A'))).mapIso e1


/-- Two actual S-linear tensor maps agree if they agree on `1 ⊗ m`.
The default tensor eliminator has only `tmul`/`add`; no generic map-class
search or zero-case elaboration is needed in the geometric consumer. -/
theorem linearMap_eq_of_one_tmul {R S M N : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f g : S ⊗[R] M →ₗ[S] N) (h : ∀ m : M, f ((1 : S) ⊗ₜ[R] m) = g ((1 : S) ⊗ₜ[R] m)) :
    f = g := by
  apply LinearMap.ext
  intro z
  induction z with
  | tmul s m =>
    have hs : (s ⊗ₜ[R] m : S ⊗[R] M) = s • ((1 : S) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hs, f.map_smul, g.map_smul, h m]
  | add x y hx hy =>
    calc
      f (x + y) = f x + f y := f.map_add' x y
      _ = g x + g y := congrArg₂ (fun a b : N => a + b) hx hy
      _ = g (x + y) := (g.map_add' x y).symm

/-- Bijectivity across an actual square of linear equivalences. This
replaces the large geometric consumer's inverse-function expansion. -/
theorem bijective_of_equiv_square {R M N P Q : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (σ : M ≃ₗ[R] N) (τ : P ≃ₗ[R] Q) (f : N →ₗ[R] P) (g : M →ₗ[R] Q)
    (hsq : τ.toLinearMap ∘ₗ f ∘ₗ σ.toLinearMap = g)
    (hg : Function.Bijective g) : Function.Bijective f := by
  constructor
  · intro x y hxy
    apply σ.symm.injective
    apply hg.1
    have hx := LinearMap.congr_fun hsq (σ.symm x)
    have hy := LinearMap.congr_fun hsq (σ.symm y)
    calc
      g (σ.symm x) = τ (f x) := by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using hx.symm
      _ = τ (f y) := congrArg τ hxy
      _ = g (σ.symm y) := by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using hy
  · intro p
    obtain ⟨m, hm⟩ := hg.2 (τ p)
    refine ⟨σ m, τ.injective ?_⟩
    exact (LinearMap.congr_fun hsq m).trans hm

/-- The actual kernel base-change map at a unit tensor, with its exact
original underlying value. The kernel membership is proved, not supplied. -/
theorem kerBaseChangeHom_one_tmul {R S M N : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (d : M →ₗ[R] N) (x : LinearMap.ker d) :
    TwoChartCech.kerBaseChangeHom d S ((1 : S) ⊗ₜ[R] x) =
      ⟨(1 : S) ⊗ₜ[R] x.1, by
        change d.baseChange S ((1 : S) ⊗ₜ[R] x.1) = 0
        rw [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp x.2, TensorProduct.tmul_zero]⟩ := by
  apply Subtype.ext
  rw [TwoChartCech.kerBaseChangeHom_apply_coe, LinearMap.baseChange_tmul]
  rfl

/-- Pure linear-algebra assembly of the actual kernel-comparison square.
The pointwise comparison is supplied by the proved geometric formula below;
no sheaf object or large presheaf construction is unfolded by this lemma. -/
theorem bijective_from_kernel_comparison
    {R S G0 G1 G2 M N M' N' : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup G0] [Module R G0] [AddCommGroup G1] [Module S G1]
    [AddCommGroup G2] [Module S G2] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module S M']
    [AddCommGroup N'] [Module S N']
    (d : M →ₗ[R] N) (d' : M' →ₗ[S] N')
    (σ : S ⊗[R] G0 ≃ₗ[S] G1) (τ : G2 ≃ₗ[S] LinearMap.ker d')
    (β : G1 →ₗ[S] G2) (ξ : G0 ≃ₗ[R] LinearMap.ker d)
    (κ : LinearMap.ker (d.baseChange S) ≃ₗ[S] LinearMap.ker d')
    (hb : Function.Bijective (TwoChartCech.kerBaseChangeHom d S))
    (hpoint : ∀ m : G0, (τ (β (σ ((1 : S) ⊗ₜ[R] m)))).1 =
      (κ (TwoChartCech.kerBaseChangeHom d S ((1 : S) ⊗ₜ[R] ξ m))).1) :
    Function.Bijective β := by
  let L : S ⊗[R] G0 →ₗ[S] LinearMap.ker d' :=
    κ.toLinearMap ∘ₗ TwoChartCech.kerBaseChangeHom d S ∘ₗ
      (LinearEquiv.baseChange R S _ _ ξ).toLinearMap
  have hsq : τ.toLinearMap ∘ₗ β ∘ₗ σ.toLinearMap = L := by
    apply linearMap_eq_of_one_tmul
    intro m
    apply Subtype.ext
    simpa only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.baseChange_tmul] using hpoint m
  have hL : Function.Bijective L :=
    κ.bijective.comp (hb.comp (LinearEquiv.baseChange R S _ _ ξ).bijective)
  exact bijective_of_equiv_square σ τ β L hsq hL

/-- At each actual open U, the base-change morphism sends the pullback
unit to the same restricted original unit. This isolates the unit and
presheaf naturality calculation from the large Cech comparison. -/
theorem baseChangeHom_unit_res (F : X.Modules) (U : X.Opens)
    (m : ΓMod ((pushforward π).obj F)) :
    let ψ := Scheme.TwoAffineOpenCover.specMap A A'
    let fA := Limits.pullback.fst π ψ
    let sA := Limits.pullback.snd π ψ
    let FA := (Scheme.Modules.pullback fA).obj F
    let β := Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ)) F
    resM FA (le_top (a := fA ⁻¹ᵁ U))
      ((β.app ⊤).hom
        ((((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app ⊤).hom m))
      = (((pullbackPushforwardAdjunction fA).unit.app F).app U).hom
        (F.presheaf.map (homOfLE (le_top (a := U))).op m) := by
  let ψ := Scheme.TwoAffineOpenCover.specMap A A'
  let fA := Limits.pullback.fst π ψ
  let sA := Limits.pullback.snd π ψ
  let FA := (Scheme.Modules.pullback fA).obj F
  let β := Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ)) F
  have h4 := unit_app_app_comp_baseChangeHom_app π ψ sA fA
    (Limits.pullback.condition (f := π) (g := ψ)) F ⊤
  have h4m := ConcreteCategory.congr_hom h4 m
  have htop : (β.app ⊤).hom
      ((((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app ⊤).hom m)
      = (((pullbackPushforwardAdjunction fA).unit.app F).app ⊤).hom m := by
    change (β.app ⊤).hom
        ((((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app ⊤).hom m) =
      (FA.presheaf.map (𝟙 (op (⊤ : (Limits.pullback π ψ).Opens)))).hom
        ((((pullbackPushforwardAdjunction fA).unit.app F).app ⊤).hom m) at h4m
    have hid : (FA.presheaf.map (𝟙 (op (⊤ : (Limits.pullback π ψ).Opens)))).hom
        ((((pullbackPushforwardAdjunction fA).unit.app F).app ⊤).hom m) =
        (((pullbackPushforwardAdjunction fA).unit.app F).app ⊤).hom m := by
      exact (ConcreteCategory.congr_hom
        (FA.presheaf.map_id (op (⊤ : (Limits.pullback π ψ).Opens)))
        ((((pullbackPushforwardAdjunction fA).unit.app F).app ⊤).hom m)).trans
        (ConcreteCategory.id_apply _)
    exact h4m.trans hid
  change resM FA (le_top (a := fA ⁻¹ᵁ U))
    ((β.app ⊤).hom
      ((((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app ⊤).hom m)) = _
  rw [htop]
  exact (Hom.app_presheaf_map ((pullbackPushforwardAdjunction fA).unit.app F)
    (homOfLE (le_top (a := U))) m).symm

section CechUnitComparison

variable (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)

local notation "ψ₀" => Scheme.TwoAffineOpenCover.specMap A A'
local notation "f₀" => Limits.pullback.fst π ψ₀
local notation "s₀" => Limits.pullback.snd π ψ₀
local notation "F₀" => CategoryTheory.Functor.obj (Scheme.Modules.pullback f₀) F
local notation "S₀" => Scheme.TwoAffineOpenCover.sectionsOf 𝒱 π F
local notation "S₁" => Scheme.TwoAffineOpenCover.sectionsOf
  (Scheme.TwoAffineOpenCover.pullback 𝒱 π A') s₀ F₀
local notation "β₀" => ModuleCat.Hom.hom (CategoryTheory.Functor.map
  (moduleSpecΓFunctor (R := CommRingCat.of A'))
  (Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ₀)) F))

/-- The unit-tensor Cech comparison at the SAME actual objects. The
chosen equivalences and their formulas are precisely the outputs of the
existing section/kernel lemmas; no IsIso or rank input is assumed here.
Their opaque parameters prevent the proof from unfolding their construction. -/
theorem baseChange_sections_unit_comparison
    (σ : A' ⊗[A] ΓMod ((pushforward π).obj F) ≃ₗ[A']
      ΓMod ((pullback ψ₀).obj ((pushforward π).obj F)))
    (hσ : ∀ m : ΓMod ((pushforward π).obj F), σ ((1 : A') ⊗ₜ[A] m) =
      ((((pullbackPushforwardAdjunction ψ₀).unit.app ((pushforward π).obj F)).app ⊤).hom m))
    (ξ : ΓMod ((pushforward π).obj F) ≃ₗ[A] LinearMap.ker (S₀).cechDiff)
    (hξ : ∀ m : ΓMod ((pushforward π).obj F), (ξ m).1 =
      (F.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op m,
       F.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op m))
    (τ : ΓMod ((pushforward s₀).obj F₀) ≃ₗ[A'] LinearMap.ker (S₁).cechDiff)
    (hτ : ∀ m : ΓMod ((pushforward s₀).obj F₀), (τ m).1 =
      ((F₀).presheaf.map (homOfLE (le_top : f₀ ⁻¹ᵁ 𝒱.U0 ≤ ⊤)).op m,
       (F₀).presheaf.map (homOfLE (le_top : f₀ ⁻¹ᵁ 𝒱.U1 ≤ ⊤)).op m))
    (κ : LinearMap.ker ((S₀).cechDiff.baseChange A') ≃ₗ[A'] LinearMap.ker (S₁).cechDiff)
    (hκ : ∀ (x : (S₀).M0 × (S₀).M1)
      (hx : (1 : A') ⊗ₜ[A] x ∈ LinearMap.ker ((S₀).cechDiff.baseChange A')),
      (κ ⟨(1 : A') ⊗ₜ[A] x, hx⟩).1 =
        ((((pullbackPushforwardAdjunction f₀).unit.app F).app 𝒱.U0).hom x.1,
         (((pullbackPushforwardAdjunction f₀).unit.app F).app 𝒱.U1).hom x.2))
    (m : ΓMod ((pushforward π).obj F)) :
    (τ (β₀ (σ ((1 : A') ⊗ₜ[A] m)))).1 =
      (κ (TwoChartCech.kerBaseChangeHom (S₀).cechDiff A' ((1 : A') ⊗ₜ[A] ξ m))).1 := by
  rw [kerBaseChangeHom_one_tmul, hκ, hσ, hτ, hξ]
  exact Prod.ext (baseChangeHom_unit_res π A' F 𝒱.U0 m)
    (baseChangeHom_unit_res π A' F 𝒱.U1 m)

end CechUnitComparison

/-- The actual global-sections map of the actual base-change morphism is
an isomorphism. This is proved separately at defaults, from the original
cover/finiteness/fibre inputs, not supplied as a new IsIso Fact. -/
theorem isIso_baseChangeHom_globalSections_of_twoAffineOpenCover
    [IsNoetherianRing A] [Flat π] (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1) :
    IsIso ((moduleSpecΓFunctor (R := .of A')).map (Scheme.Modules.baseChangeHom
      (Limits.pullback.condition (f := π) (g := Scheme.TwoAffineOpenCover.specMap A A')) F)) := by
  set ψ := Scheme.TwoAffineOpenCover.specMap A A' with hψ
  set fA := Limits.pullback.fst π ψ
  set sA := Limits.pullback.snd π ψ
  set FA := (Scheme.Modules.pullback fA).obj F
  classical
  set β := Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ)) F with hβ
  set S := 𝒱.sectionsOf π F with hS
  set SA := (𝒱.pullback π A').sectionsOf sA FA with hSA
  have flat_sections : ∀ (U : X.Opens), IsAffineOpen U →
      letI := moduleSectionsOfHom π F U; Module.Flat A Γ(F, U) := by
    intro U hU
    letI := algebraOfHom π U
    letI := moduleSectionsOfHom π F U
    haveI : IsScalarTower A Γ(X, U) Γ(F, U) := isScalarTower_sections π F U
    haveI : Module.Flat A Γ(X, U) := flat_sections_of_flat π U hU
    haveI : Module.Projective Γ(X, U) Γ(F, U) := projective_sections_of_locallyTrivial F htriv ⟨U, hU⟩
    exact Module.Flat.trans A Γ(X, U) Γ(F, U)
  haveI : Module.Flat A S.M0 := flat_sections 𝒱.U0 𝒱.isAffineOpen_U0
  haveI : Module.Flat A S.M1 := flat_sections 𝒱.U1 𝒱.isAffineOpen_U1
  haveI : Module.Flat A S.M01 := flat_sections (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
  haveI : Module.Flat A (S.M0 × S.M1) := Module.Flat.prod_of_flat S.M0 S.M1
  haveI : Module.Finite A (LinearMap.ker S.cechDiff) := hfin.1
  haveI : Module.Finite A (S.M01 ⧸ LinearMap.range S.cechDiff) := hfin.2
  have hsq : ∀ (K : Type u) [Field K] [Algebra A K], Function.Surjective (S.cechDiff.baseChange K) := by
    intro K _ _
    refine (exists_linearEquiv_ker_baseChange_cechDiff π K 𝒱 F htriv).1 ?_
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hfib K
  obtain ⟨-, hbc, -⟩ := TwoChartCech.Mumford.projective_ker_of_fibre_surjective S.cechDiff hsq
  have hb : Function.Bijective (TwoChartCech.kerBaseChangeHom S.cechDiff A') := hbc A'
  obtain ⟨-, κ, hκ⟩ := exists_linearEquiv_ker_baseChange_cechDiff π A' 𝒱 F htriv
  obtain ⟨σ, hσ⟩ := exists_linearEquiv_tensor_ΓMod_pullback A' ((pushforward π).obj F)
    (isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv)
  letI := moduleSectionsOfHom π F ⊤
  letI := moduleSectionsOfHom sA FA ⊤
  obtain ⟨eX, heX⟩ := exists_linearEquiv_sectionsOf_H0 𝒱 π F
  obtain ⟨eP, heP⟩ := exists_linearEquiv_sectionsOf_H0 (𝒱.pullback π A') sA FA
  let gX := globalSectionsEquiv π F
  let gP := globalSectionsEquiv sA FA
  let Γβ : ΓMod ((pullback ψ).obj ((pushforward π).obj F)) →ₗ[A'] ΓMod ((pushforward sA).obj FA) :=
    ((moduleSpecΓFunctor (R := .of A')).map β).hom
  let ξ : ΓMod ((pushforward π).obj F) ≃ₗ[A] LinearMap.ker S.cechDiff := gX.trans eX
  let τ : ΓMod ((pushforward sA).obj FA) ≃ₗ[A'] LinearMap.ker SA.cechDiff := gP.trans eP
  have hξ : ∀ m : ΓMod ((pushforward π).obj F), (ξ m).1 =
      (F.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op m,
       F.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op m) := by
    intro m
    change (eX (gX m)).1 = _
    exact heX (gX m)
  have hτ : ∀ m : ΓMod ((pushforward sA).obj FA), (τ m).1 =
      (FA.presheaf.map (homOfLE (le_top : fA ⁻¹ᵁ 𝒱.U0 ≤ ⊤)).op m,
       FA.presheaf.map (homOfLE (le_top : fA ⁻¹ᵁ 𝒱.U1 ≤ ⊤)).op m) := by
    intro m
    change (eP (gP m)).1 = _
    exact heP (gP m)
  have hpoint := baseChange_sections_unit_comparison π A' 𝒱 F σ hσ ξ hξ τ hτ κ hκ
  have hbij : Function.Bijective Γβ :=
    bijective_from_kernel_comparison S.cechDiff SA.cechDiff σ τ Γβ ξ κ hb hpoint
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

theorem isIso_baseChangeHom_of_twoAffineOpenCover_aux
    [IsNoetherianRing A] [Flat π] (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1) :
    IsIso (Scheme.Modules.baseChangeHom
      (Limits.pullback.condition (f := π) (g := Scheme.TwoAffineOpenCover.specMap A A')) F) := by
  set ψ := Scheme.TwoAffineOpenCover.specMap A A' with hψ
  set fA := Limits.pullback.fst π ψ
  set sA := Limits.pullback.snd π ψ
  set FA := (Scheme.Modules.pullback fA).obj F

  have hsrc : IsIso (Scheme.Modules.fromTildeΓ (R := .of A') ((pullback ψ).obj ((pushforward π).obj F))) :=
    isIso_fromTildeΓ_pullback_pushforward π A' F
      (isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv)

  have htrivA : ∀ x : (Limits.pullback π ψ : Scheme.{u}), ∃ (V : (Limits.pullback π ψ).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj FA ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :=
    ((⟨htriv⟩ : Scheme.Modules.IsInvertible F).pullback fA).exists_trivialization
  have htgt : IsIso (Scheme.Modules.fromTildeΓ (R := .of A') ((pushforward sA).obj FA)) :=
    isIso_fromTildeGamma_pushforward_of_locallyTrivial sA (𝒱.pullback π A') FA htrivA

  have key := isIso_baseChangeHom_globalSections_of_twoAffineOpenCover π A' 𝒱 F htriv hfin hfib
  exact isIso_of_isIso_moduleSpecΓFunctor_map hsrc htgt _ key

end main

end AlgebraicGeometry.Scheme.Modules
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme.Modules"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry"

open _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme.Modules in
r2nos_open_dual "_root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme.Modules" in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A)) [Flat π]
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1)
    (A' : Type u) [CommRing A'] [Algebra A A'] {X' : Scheme.{u}} (π' : X' ⟶ Spec (.of A')) (g' : X' ⟶ X)
    (hcart : IsPullback g' π' π (Scheme.TwoAffineOpenCover.specMap A A')) :
    IsIso (Scheme.Modules.baseChangeHom hcart.w F) :=
  (Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback hcart
    (IsPullback.of_hasPullback π (Scheme.TwoAffineOpenCover.specMap A A')) F).mpr
    (isIso_baseChangeHom_of_twoAffineOpenCover_aux π A' 𝒱 F htriv hfin hfib)

#print axioms solution
end S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
