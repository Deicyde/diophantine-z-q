-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Picard.NormalizedDescent.DescentDataModules), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged except that the `AlgebraicGeometry.baseChangeDiagram*`, `baseChangeCone*` and `baseChangeMap*` declarations are renamed into `AlgebraicGeometry.JacobianChallenge` (CloudW07 edit, to avoid a clash with vendored Stacks names).
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.NormalizedDescent.DescentData
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.NormalizedDescent.Modules

/-!
# Normalized descent data of invertible modules

Normalized transition isomorphisms assemble compatible invertible module sheaves into an actual descent datum.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Scheme

section DescentDatumModules

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom}
  (hs : ∀ Y, s Y ≫ pullback.snd f Y.hom = 𝟙 _)
  (hsb : ∀ {Y Z : Over S} (w : Y ⟶ Z), s Y ≫ JacobianChallenge.baseChangeMap f w = w.left ≫ s Z)
  (hsurj : ∀ Y : Over S, Function.Surjective (pullback.snd f Y.hom).appTop)
  {T : Over S} {ι : Type*} {T' : ι → Over S} {g : ∀ i, T' i ⟶ T}
  {N : modulesPseudofunctor.obj (.mk (op T.left))}
  {L : ∀ i, modulesPseudofunctor.obj (.mk (op (pullback f (T' i).hom)))}
  [hL : ∀ i, (L i).IsInvertible]
  (α : ∀ i, (modulesPseudofunctor.map (s (T' i)).op.toLoc).toFunctor.obj
    (L i) ≅ (modulesPseudofunctor.map (g i).left.op.toLoc).toFunctor.obj N)
  (e : ∀ i j,
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁.op.toLoc).toFunctor.obj
      (L i) ≅
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂.op.toLoc).toFunctor.obj
      (L j))

include hs hsb e in
/-- There are normalized gluing isomorphisms on the double overlaps. -/
lemma exists_isSectionNormalized_gluing (i j : ι) :
    ∃ φ, IsIso φ ∧ IsSectionNormalized s g α (hsb (pullback.fst (g i) (g j)))
      (hsb (pullback.snd (g i) (g j))) (q := (pullback.fst (g i) (g j) ≫ g i).left) rfl
      (by rw [← Over.comp_left, ← pullback.condition]) φ :=
  exists_isSectionNormalized (hs _) _ _ _ _ (e i j)

/-- The normalized gluing isomorphisms. -/
noncomputable def normalizedGluing (i j : ι) :
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁.op.toLoc).toFunctor.obj
      (L i) ⟶
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂.op.toLoc).toFunctor.obj
      (L j) :=
  (exists_isSectionNormalized_gluing hs hsb α e i j).choose

instance (i j : ι) : IsIso (normalizedGluing hs hsb α e i j) :=
  (exists_isSectionNormalized_gluing hs hsb α e i j).choose_spec.1

/-- The descent datum, relative to the family `X_{T i} ⟶ X_T`, formed by the modules `L i` and
the normalized gluing isomorphisms `normalizedGluing`. -/
noncomputable def normalizedDescentData :
    modulesPseudofunctor.DescentData' (fun i j ↦ chosenPullbackBaseChangeMap f (g i) (g j))
      (fun i j k ↦ chosenPullback₃BaseChangeMap f g i j k) :=
  descentDataOfIsSectionNormalized hsb (α := α)
    (fun hψ hφ hψ' ↦ have := hψ; IsSectionNormalized.eq (hs _) (hsurj _) hφ hψ')
    (normalizedGluing hs hsb α e)
    (fun i j ↦ (exists_isSectionNormalized_gluing hs hsb α e i j).choose_spec.2)

end DescentDatumModules

end AlgebraicGeometry
