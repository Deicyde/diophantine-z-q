/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

structure SubPicCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Type (u + 1) where

  P : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), RigidifiedLineBundle c ε t → Prop
  unit_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), P t (RigidifiedLineBundle.unit t)
  congr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t),
    Nonempty (M.L ≅ M'.L) → P t M → P t M'
  pullback_mem : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t), P t M → P t' (M.pullbackAlong ψ)

def SubPicCondition.top (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ _ => True
  unit_mem := fun _ => trivial
  congr := fun _ _ _ _ _ => trivial
  pullback_mem := fun _ _ _ _ _ => trivial

structure RepresentsRelSubPic (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) (D : RelativePic0Designation R c) : Type (u + 1) where

  poincare : RigidifiedLineBundle c ε D.toBase
  poincare_mem : P.P D.toBase poincare

  univ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t), P.P t M →
    ∃! g : SchemeHomOver t D.toBase, Nonempty ((poincare.pullbackAlong g).L ≅ M.L)

  zero : Nonempty ((poincare.pullbackAlong ⟨D.zeroSection, D.zeroSection_toBase⟩).L ≅
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 _)).L)

namespace RepresentsRelSubPic

variable {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

noncomputable def classify (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) : SchemeHomOver t D.toBase :=
  (h.univ t M hM).choose

theorem classify_spec (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) :
    Nonempty ((h.poincare.pullbackAlong (h.classify t M hM)).L ≅ M.L) :=
  (h.univ t M hM).choose_spec.1

theorem classify_unique (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) (g : SchemeHomOver t D.toBase)
    (hg : Nonempty ((h.poincare.pullbackAlong g).L ≅ M.L)) : g = h.classify t M hM :=
  (h.univ t M hM).unique hg (h.classify_spec t M hM)

theorem ext_of_iso (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (g g' : SchemeHomOver t D.toBase)
    (hgg' : Nonempty ((h.poincare.pullbackAlong g).L ≅ (h.poincare.pullbackAlong g').L)) : g = g' := by
  have hmem : P.P t (h.poincare.pullbackAlong g') := P.pullback_mem _ _ g' _ h.poincare_mem
  have h1 := h.classify_unique t _ hmem g hgg'
  have h2 := h.classify_unique t _ hmem g' ⟨Iso.refl _⟩
  exact h1.trans h2.symm

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard
