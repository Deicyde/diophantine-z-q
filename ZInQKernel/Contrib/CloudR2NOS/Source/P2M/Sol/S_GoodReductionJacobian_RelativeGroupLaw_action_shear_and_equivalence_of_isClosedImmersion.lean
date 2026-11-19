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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.lean
  Source sha256  : 8c1182e836acf3ab11c694df5028b798065e9a4ff5959e69278e879f9415012f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
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

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace G1AuxFFX
r2nos_namespace_dual

open GoodReductionJacobian.RelativeGroupLaw
r2nos_open_dual "GoodReductionJacobian.RelativeGroupLaw"

variable {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left (G := SchemeHomOver t' f) h

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (v w : T ⟶ G) (hv : v ≫ f = t) (hw : w ≫ f = t) (hv' : v ≫ f = t') (hw' : w ≫ f = t') :
    (L.mul t ⟨v, hv⟩ ⟨w, hw⟩).1 = (L.mul t' ⟨v, hv'⟩ ⟨w, hw'⟩).1 := by
  subst h; rfl

theorem inv_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (v : T ⟶ G) (hv : v ≫ f = t) (hv' : v ≫ f = t') :
    (L.inv t ⟨v, hv⟩).1 = (L.inv t' ⟨v, hv'⟩).1 := by
  subst h; rfl

variable (L : RelativeGroupLaw R f) {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw R (i ≫ f))

theorem hom_one
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = L.one t := by
  letI := L.pointGroup t
  have h := hi t (LN.one t) (LN.one t)
  rw [LN.one_mul] at h

  have : L.mul t (NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) (L.one t) =
      L.mul t (NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
        (NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by
    rw [L.mul_one]; exact h
  exact (mul_left_cancel (G := SchemeHomOver t f) this).symm

theorem hom_inv
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : SchemeHomOver t (i ≫ f)) :
    NeronModelInfra.schemeHomOverComp (LN.inv t n) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
      L.inv t (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by
  letI := L.pointGroup t
  have h := hi t (LN.inv t n) n
  rw [LN.inv_mul_cancel, hom_one L i LN hi] at h
  exact eq_inv_of_mul_eq_one_left (G := SchemeHomOver t f) h.symm

theorem comp_action {T : Scheme.{u}} (φ : T ⟶ pullback (i ≫ f) f) :
    φ ≫ L.action i =
      (L.mul (φ ≫ actionSource f i)
        (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionFstPoint i))
        (GoodReductionJacobian.schemeHomOverComp φ rfl (L.actionSndPoint i))).1 :=
  congrArg Subtype.val (L.mul_natural _ _ φ rfl (L.actionFstPoint i) (L.actionSndPoint i))

theorem comp_action' {T : Scheme.{u}} (φ : T ⟶ pullback (i ≫ f) f) (t : T ⟶ Spec (CommRingCat.of R))
    (ht : φ ≫ actionSource f i = t) :
    φ ≫ L.action i =
      (L.mul t ⟨φ ≫ pullback.fst (i ≫ f) f ≫ i, by rw [← ht, Category.assoc, Category.assoc, pullback.condition]⟩
        ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [← ht, Category.assoc]⟩).1 := by
  rw [comp_action L i φ]
  exact mul_val_congr L ht _ _ _ _ _ _

def shearHom : pullback (i ≫ f) f ⟶ pullback (i ≫ f) f :=
  pullback.lift (pullback.fst (i ≫ f) f) (L.action i)
    (by rw [L.action_over]; exact pullback.condition)

def shearInv : pullback (i ≫ f) f ⟶ pullback (i ≫ f) f :=
  pullback.lift (pullback.fst (i ≫ f) f)
    (L.mul (actionSource f i) (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i)).1
    (by rw [(L.mul (actionSource f i) _ _).2]; exact pullback.condition)

@[scoped simp] theorem shearHom_fst : shearHom L i ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f := pullback.lift_fst _ _ _
@[scoped simp] theorem shearHom_snd : shearHom L i ≫ pullback.snd (i ≫ f) f = L.action i := pullback.lift_snd _ _ _
@[scoped simp] theorem shearInv_fst : shearInv L i ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f := pullback.lift_fst _ _ _
@[scoped simp] theorem shearInv_snd : shearInv L i ≫ pullback.snd (i ≫ f) f =
    (L.mul (actionSource f i) (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i)).1 :=
  pullback.lift_snd _ _ _

theorem shearHom_src : shearHom L i ≫ actionSource f i = actionSource f i := by
  show shearHom L i ≫ pullback.snd (i ≫ f) f ≫ f = pullback.snd (i ≫ f) f ≫ f
  rw [← Category.assoc, shearHom_snd, L.action_over]

theorem shearInv_src : shearInv L i ≫ actionSource f i = actionSource f i := by
  show shearInv L i ≫ pullback.snd (i ≫ f) f ≫ f = pullback.snd (i ≫ f) f ≫ f
  rw [← Category.assoc, shearInv_snd, (L.mul (actionSource f i) _ _).2]

def shear : pullback (i ≫ f) f ≅ pullback (i ≫ f) f where
  hom := shearHom L i
  inv := shearInv L i
  hom_inv_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearHom L i) (shearHom_src L i) (L.actionFstPoint i) =
        L.actionFstPoint i := Subtype.ext (by
          show shearHom L i ≫ pullback.fst (i ≫ f) f ≫ i = pullback.fst (i ≫ f) f ≫ i
          rw [← Category.assoc, shearHom_fst])
    have hb : GoodReductionJacobian.schemeHomOverComp (shearHom L i) (shearHom_src L i) (L.actionSndPoint i) =
        L.mul (actionSource f i) (L.actionFstPoint i) (L.actionSndPoint i) :=
      Subtype.ext ((shearHom_snd L i).trans (L.action_def i))
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearInv_fst, shearHom_fst]
    · rw [Category.id_comp, Category.assoc, shearInv_snd]
      have := congrArg Subtype.val (L.mul_natural _ _ (shearHom L i) (shearHom_src L i)
        (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, inv_natural, ha, hb, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
      rfl
  inv_hom_id := by
    have ha : GoodReductionJacobian.schemeHomOverComp (shearInv L i) (shearInv_src L i) (L.actionFstPoint i) =
        L.actionFstPoint i := Subtype.ext (by
          show shearInv L i ≫ pullback.fst (i ≫ f) f ≫ i = pullback.fst (i ≫ f) f ≫ i
          rw [← Category.assoc, shearInv_fst])
    have hb : GoodReductionJacobian.schemeHomOverComp (shearInv L i) (shearInv_src L i) (L.actionSndPoint i) =
        L.mul (actionSource f i) (L.inv (actionSource f i) (L.actionFstPoint i)) (L.actionSndPoint i) :=
      Subtype.ext (shearInv_snd L i)
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, shearHom_fst, shearInv_fst]
    · rw [Category.id_comp, Category.assoc, shearHom_snd, L.action_def]
      have := congrArg Subtype.val (L.mul_natural _ _ (shearInv L i) (shearInv_src L i)
        (L.actionFstPoint i) (L.actionSndPoint i))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, ha, hb, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul]
      rfl

end G1AuxFFX
w03_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.G1AuxFFX"

end
w03_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.G1AuxFFX"

open G1AuxFFX GoodReductionJacobian.RelativeGroupLaw in
r2nos_open_dual "G1AuxFFX GoodReductionJacobian.RelativeGroupLaw" in
theorem solution
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    L.action i ≫ f = CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ f ∧
    (∃ σ : CategoryTheory.Limits.pullback (i ≫ f) f ≅ CategoryTheory.Limits.pullback (i ≫ f) f,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = L.action i ∧
      σ.hom ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) f = CategoryTheory.Limits.pullback.fst (i ≫ f) f) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f),
      a ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = b ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f → a ≫ L.action i = b ≫ L.action i → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ G =>
      ∃ φ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f, φ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = x ∧ φ ≫ L.action i = y) := by
  refine ⟨L.action_over i, ⟨shear L i, shearHom_snd L i, shearHom_fst L i⟩, ?_, ?_⟩
  ·
    intro T a b hs ht
    apply pullback.hom_ext _ hs

    let t : T ⟶ Spec (CommRingCat.of R) := a ≫ actionSource f i
    have hbt : b ≫ actionSource f i = t := by
      show b ≫ pullback.snd (i ≫ f) f ≫ f = a ≫ pullback.snd (i ≫ f) f ≫ f
      rw [← Category.assoc, ← hs, Category.assoc]
    rw [comp_action' L i a t rfl, comp_action' L i b t hbt] at ht
    letI := L.pointGroup t
    have hx : (⟨b ≫ pullback.snd (i ≫ f) f, by rw [← hbt, Category.assoc]⟩ : SchemeHomOver t f) =
        ⟨a ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩ := Subtype.ext hs.symm
    rw [hx] at ht
    have := mul_right_cancel (G := SchemeHomOver t f) (Subtype.ext ht)
    have h1 : (a ≫ pullback.fst (i ≫ f) f) ≫ i = (b ≫ pullback.fst (i ≫ f) f) ≫ i := by
      simpa only [Category.assoc] using congrArg Subtype.val this
    exact (cancel_mono i).mp h1
  ·
    intro T
    refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    ·
      refine ⟨pullback.lift (LN.one (x ≫ f)).1 x (LN.one (x ≫ f)).2, pullback.lift_snd _ _ _, ?_⟩
      rw [comp_action' L i _ (x ≫ f) (by
        show pullback.lift (LN.one (x ≫ f)).1 x (LN.one (x ≫ f)).2 ≫ pullback.snd (i ≫ f) f ≫ f = x ≫ f
        rw [← Category.assoc, pullback.lift_snd])]
      have key : L.mul (x ≫ f) (NeronModelInfra.schemeHomOverComp (LN.one (x ≫ f)) ⟨i, rfl⟩) ⟨x, rfl⟩ = ⟨x, rfl⟩ := by
        rw [hom_one L i LN hi, L.one_mul]
      refine Eq.trans ?_ (congrArg Subtype.val key)
      congr 2 <;> apply Subtype.ext
      · show pullback.lift (LN.one (x ≫ f)).1 x _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.one (x ≫ f)).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · exact pullback.lift_snd _ _ _
    ·
      obtain ⟨φ, rfl, rfl⟩ := hxy
      let t : T ⟶ Spec (CommRingCat.of R) := φ ≫ actionSource f i
      let n : SchemeHomOver t (i ≫ f) := ⟨φ ≫ pullback.fst (i ≫ f) f, by
        show (φ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = φ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      let x : SchemeHomOver t f := ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩
      have hact : φ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n ⟨i, rfl⟩) x).1 :=
        (comp_action' L i φ t rfl).trans (mul_val_congr L rfl _ _ _ _ _ _)
      refine ⟨pullback.lift (LN.inv t n).1 (φ ≫ L.action i)
        (by rw [(LN.inv t n).2, Category.assoc, L.action_over]), pullback.lift_snd _ _ _, ?_⟩
      have hsrc : pullback.lift (LN.inv t n).1 (φ ≫ L.action i)
          (by rw [(LN.inv t n).2, Category.assoc, L.action_over]) ≫ actionSource f i = t := by
        show _ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, pullback.lift_snd, Category.assoc, L.action_over]
      rw [comp_action' L i _ t hsrc]
      letI := L.pointGroup t
      have key : L.mul t (NeronModelInfra.schemeHomOverComp (LN.inv t n) ⟨i, rfl⟩)
          (L.mul t (NeronModelInfra.schemeHomOverComp n ⟨i, rfl⟩) x) = x := by
        rw [hom_inv L i LN hi, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
      refine Eq.trans ?_ (congrArg Subtype.val key)
      congr 2 <;> apply Subtype.ext
      · show pullback.lift (LN.inv t n).1 (φ ≫ L.action i) _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.inv t n).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · show pullback.lift (LN.inv t n).1 (φ ≫ L.action i) _ ≫ pullback.snd (i ≫ f) f = (L.mul t _ x).1
        rw [pullback.lift_snd, hact]
    ·
      obtain ⟨φ, rfl, rfl⟩ := hxy
      obtain ⟨ψ, hψ, rfl⟩ := hyz
      let t : T ⟶ Spec (CommRingCat.of R) := φ ≫ actionSource f i
      let n₁ : SchemeHomOver t (i ≫ f) := ⟨φ ≫ pullback.fst (i ≫ f) f, by
        show (φ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = φ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      let x : SchemeHomOver t f := ⟨φ ≫ pullback.snd (i ≫ f) f, by rw [Category.assoc]⟩
      have hψt : ψ ≫ actionSource f i = t := by
        show ψ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, hψ, Category.assoc, L.action_over]
      let n₂ : SchemeHomOver t (i ≫ f) := ⟨ψ ≫ pullback.fst (i ≫ f) f, by
        rw [← hψt]
        show (ψ ≫ pullback.fst (i ≫ f) f) ≫ i ≫ f = ψ ≫ pullback.snd (i ≫ f) f ≫ f
        rw [Category.assoc, pullback.condition]⟩
      have hact1 : φ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n₁ ⟨i, rfl⟩) x).1 :=
        (comp_action' L i φ t rfl).trans (mul_val_congr L rfl _ _ _ _ _ _)
      have hact2 : ψ ≫ L.action i = (L.mul t (NeronModelInfra.schemeHomOverComp n₂ ⟨i, rfl⟩)
          (L.mul t (NeronModelInfra.schemeHomOverComp n₁ ⟨i, rfl⟩) x)).1 := by
        rw [comp_action' L i ψ t hψt]
        congr 2
        apply Subtype.ext
        show ψ ≫ pullback.snd (i ≫ f) f = _
        rw [hψ, hact1]
      refine ⟨pullback.lift (LN.mul t n₂ n₁).1 (φ ≫ pullback.snd (i ≫ f) f)
        (by rw [(LN.mul t n₂ n₁).2, Category.assoc]), pullback.lift_snd _ _ _, ?_⟩
      have hsrc : pullback.lift (LN.mul t n₂ n₁).1 (φ ≫ pullback.snd (i ≫ f) f)
          (by rw [(LN.mul t n₂ n₁).2, Category.assoc]) ≫ actionSource f i = t := by
        show _ ≫ pullback.snd (i ≫ f) f ≫ f = t
        rw [← Category.assoc, pullback.lift_snd, Category.assoc]
      rw [comp_action' L i _ t hsrc, hact2, ← L.mul_assoc, ← hi]
      congr 2 <;> apply Subtype.ext
      · show pullback.lift (LN.mul t n₂ n₁).1 _ _ ≫ pullback.fst (i ≫ f) f ≫ i = (LN.mul t n₂ n₁).1 ≫ i
        rw [← Category.assoc, pullback.lift_fst]
      · exact pullback.lift_snd _ _ _

#print axioms solution
end S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
