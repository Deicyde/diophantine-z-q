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
  Source file    : Definitions/Def_AlgebraicGeometry_RelSubPicPresheaf.lean
  Source sha256  : 45a84c29955ec8c6fe66cac91563ad46700c26b8efb728be338084092b28da9d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.RelPicard
r2nos_namespace_dual

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite
r2nos_open_dual "CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite"

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

namespace RigidifiedLineBundle
r2nos_namespace_dual

noncomputable def pullbackAlongPullbackAlongIso {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    ((M.pullbackAlong ψ).pullbackAlong φ).L ≅ (M.pullbackAlong (postComp ψ φ)).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ψ φ)).app M.L

noncomputable def pullbackAlongIdIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) :
    (M.pullbackAlong ⟨𝟙 T, Category.id_comp t⟩).L ≅ M.L :=
  (Scheme.Modules.pullbackCongr (baseChangeSnd_id c t)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

end RigidifiedLineBundle

namespace SubPicCondition
r2nos_namespace_dual

def onClasses (P : SubPicCondition c ε) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    RigidifiedLineBundle.Classes c ε t → Prop :=
  Quotient.lift (P.P t) fun M M' h => propext ⟨P.congr t M M' h, P.congr t M' M ⟨h.some.symm⟩⟩

@[simp] theorem onClasses_mk (P : SubPicCondition c ε) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) : P.onClasses t (Quotient.mk _ M) ↔ P.P t M := Iff.rfl

theorem onClasses_classesMap (P : SubPicCondition c ε) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (x : RigidifiedLineBundle.Classes c ε t)
    (hx : P.onClasses t x) : P.onClasses t' (RigidifiedLineBundle.classesMap ψ x) := by
  induction x using Quotient.ind
  exact P.pullback_mem _ _ ψ _ hx

end SubPicCondition

def relSubPicSubfunctor (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) : Subfunctor (relPicardPresheaf c ε) where
  obj X := {x | P.onClasses X.unop.hom x}
  map φ := fun x hx => P.onClasses_classesMap ⟨φ.unop.left, Over.w φ.unop⟩ x hx

def relSubPicPresheaf (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) :=
  (relSubPicSubfunctor c ε P).toFunctor

namespace RepresentsRelSubPic
r2nos_namespace_dual

variable {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

def pullbackClass (h : RepresentsRelSubPic c ε P D) (X : Over (Spec (CommRingCat.of R)))
    (g : X ⟶ Over.mk D.toBase) : (relSubPicPresheaf c ε P).obj (op X) :=
  ⟨Quotient.mk _ (h.poincare.pullbackAlong ⟨g.left, Over.w g⟩), P.pullback_mem _ _ _ _ h.poincare_mem⟩

noncomputable def classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t) (hx : P.onClasses t x) :
    SchemeHomOver t D.toBase :=
  h.classify t x.out (by rwa [← Quotient.out_eq x] at hx)

theorem eq_classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t) (hx : P.onClasses t x)
    (g : SchemeHomOver t D.toBase) (hg : Quotient.mk _ (h.poincare.pullbackAlong g) = x) :
    g = h.classifyClass t x hx := by
  refine h.classify_unique t _ _ g ?_
  rw [← Quotient.out_eq x] at hg
  exact Quotient.exact hg

theorem mk_pullbackAlong_classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t) (hx : P.onClasses t x) :
    Quotient.mk _ (h.poincare.pullbackAlong (h.classifyClass t x hx)) = x := by
  conv_rhs => rw [← Quotient.out_eq x]
  exact Quotient.sound (h.classify_spec t _ _)

noncomputable def representableBy (h : RepresentsRelSubPic c ε P D) :
    (relSubPicPresheaf c ε P).RepresentableBy (Over.mk D.toBase) where
  homEquiv {X} :=
    { toFun := fun g => h.pullbackClass X g
      invFun := fun x => Over.homMk (h.classifyClass X.hom x.1 x.2).1 (h.classifyClass X.hom x.1 x.2).2
      left_inv := fun g => Over.OverMorphism.ext (congrArg Subtype.val
        (h.eq_classifyClass X.hom _ _ ⟨g.left, Over.w g⟩ rfl)).symm
      right_inv := fun x => Subtype.ext (h.mk_pullbackAlong_classifyClass X.hom x.1 x.2) }
  homEquiv_comp {X X'} f g := by
    apply Subtype.ext
    apply Quotient.sound
    exact ⟨(h.poincare.pullbackAlongPullbackAlongIso ⟨g.left, Over.w g⟩ ⟨f.left, Over.w f⟩).symm⟩

end RepresentsRelSubPic

@[simp] theorem relSubPicPresheaf_map_coe {P : SubPicCondition c ε} {X X' : (Over (Spec (CommRingCat.of R)))ᵒᵖ}
    (φ : X ⟶ X') (x : (relSubPicPresheaf c ε P).obj X) :
    ((relSubPicPresheaf c ε P).map φ x).1 = RigidifiedLineBundle.classesMap ⟨φ.unop.left, Over.w φ.unop⟩ x.1 :=
  rfl

namespace RepresentsRelSubPic
r2nos_namespace_dual

variable {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

theorem nonempty_of_representableBy (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk D.toBase))
    (h0 : (e.homEquiv (Over.homMk D.zeroSection D.zeroSection_toBase :
        Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _))) :
    Nonempty (RepresentsRelSubPic c ε P D) := by

  let u := e.homEquiv (𝟙 (Over.mk D.toBase))
  let Q : RigidifiedLineBundle c ε D.toBase := u.1.out
  have hQ : P.P D.toBase Q := by
    have h2 : P.onClasses D.toBase u.1 := u.2
    rwa [← Quotient.out_eq u.1] at h2

  have key : ∀ (X : Over (Spec (CommRingCat.of R))) (g : X ⟶ Over.mk D.toBase),
      (e.homEquiv g).1 = Quotient.mk _ (Q.pullbackAlong ⟨g.left, Over.w g⟩) := by
    intro X g
    have hc := e.homEquiv_comp g (𝟙 _)
    rw [Category.comp_id] at hc
    rw [hc, relSubPicPresheaf_map_coe]
    change RigidifiedLineBundle.classesMap _ u.1 = _
    conv_lhs => rw [← Quotient.out_eq u.1]
    rfl
  refine ⟨{ poincare := Q, poincare_mem := hQ, univ := ?_, zero := ?_ }⟩
  · intro T t M hM
    let x : (relSubPicPresheaf c ε P).obj (op (Over.mk t)) := ⟨Quotient.mk _ M, hM⟩
    let g : Over.mk t ⟶ Over.mk D.toBase := e.homEquiv.symm x
    have hg : e.homEquiv g = x := e.homEquiv.apply_symm_apply x
    refine ⟨⟨g.left, Over.w g⟩, ?_, fun g'' hg'' => ?_⟩
    · have h1 : (e.homEquiv g).1 = Quotient.mk _ M := congrArg Subtype.val hg
      rw [key] at h1
      exact Quotient.exact h1
    · have h2 : e.homEquiv (Over.homMk g''.1 g''.2 : Over.mk t ⟶ Over.mk D.toBase) = x := by
        apply Subtype.ext
        rw [key]
        exact Quotient.sound hg''
      have h3 : (Over.homMk g''.1 g''.2 : Over.mk t ⟶ Over.mk D.toBase) = g :=
        e.homEquiv.injective (h2.trans hg.symm)
      exact Subtype.ext (congrArg (fun k => k.left) h3)
  · have h1 := h0
    rw [key] at h1
    exact Quotient.exact h1

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
