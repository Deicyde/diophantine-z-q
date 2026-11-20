/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Data.Finite.Sum
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ZInQKernel.Contrib.CloudB3W17bOka.Oka.CategoryTheory.Sites.Over

/-!
# Sheaves of modules of finite type: transport, quotients, change of site, locality

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean`; see `README.md` on the
mirror tree. That file imports none of `Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Mathlib.Data.Finite.Sum`, `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` or
`Mathlib.CategoryTheory.Limits.Constructions.Over.Products`, so upstreaming this file adds those
four imports — **ten** files to the target's own transitive closure, measured rather than
estimated, with the target's closure as the baseline rather than this file's. The two `Oka`
imports cost nothing beyond that: `Oka/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`
and `Oka/CategoryTheory/Sites/Over.lean` are themselves mirror files whose targets are already in
the closure — though the first of those carries an import cost of its own, recorded in its module
docstring.

Mathlib defines `SheafOfModules.GeneratingSections`, `SheafOfModules.LocalGeneratorsData` and the
predicate `SheafOfModules.IsFiniteType`, and proves that generating sections push forward along an
epimorphism. What it does not have, and what every finiteness argument in this development needs,
is the **stability** of `SheafOfModules.IsFiniteType`. That is this file, in six groups.

* **Transport.** `SheafOfModules.IsFiniteType.of_iso` and
  `SheafOfModules.isFiniteType_of_isIso`, packaged as the `CategoryTheory.ObjectProperty`
  `SheafOfModules.isFiniteType` with its `IsClosedUnderIsomorphisms` instance.
* **Quotients.** `SheafOfModules.IsFiniteType.of_epi`, that the target of an epimorphism out of a
  sheaf of finite type is of finite type, and its slicewise form
  `SheafOfModules.IsFiniteType.of_epi_over`.
* **Change of site.** `SheafOfModules.LocalGeneratorsData.pushforward` and
  `SheafOfModules.isFiniteType_pushforward`, with the sharper
  `SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint` for a pushforward that has the extra
  adjoint.
* **Locality.** `SheafOfModules.LocalGeneratorsData.bind` refines a cover by a cover, and
  `SheafOfModules.IsFiniteType.of_coversTop` draws the conclusion: finite type over every member
  of a family covering the top is finite type. `SheafOfModules.IsFiniteType.over` is the single
  slice in the other direction, and `SheafOfModules.IsFiniteType.of_coversTop_of_forall` is the
  form that quantifies over the covering family rather than taking one.
* **Biproducts and free sheaves.** `SheafOfModules.freeGeneratingSections`,
  `SheafOfModules.GeneratingSections.biprod`, `SheafOfModules.IsFiniteType.of_generatingSections`,
  and `SheafOfModules.isFiniteType_free_biprod` with its slicewise companion
  `SheafOfModules.isFiniteType_over_free_biprod`: a finite free sheaf plus a sheaf of finite type
  is of finite type.
* **The iterated slice.** Four statements transporting `SheafOfModules.IsFiniteType` across
  `SheafOfModules.overOverEquivalence`, and `SheafOfModules.GeneratingSections.restrict`, which
  moves generating sections along a morphism of the site.

The consumers are `Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Basic.lean`,
`Oka/Algebra/Category/ModuleCat/Sheaf/LocallySurjective.lean` and
`Oka/AlgebraicGeometry/Modules/Tilde.lean`, the last of which reduces finiteness of the module of
global sections on a `Spec` to finiteness over a distinguished open.

**Every named declaration below now carries a docstring.** Nineteen of the thirty-one did not
until taxis #906; eleven of those were `lemma`s and have been written. The remaining eight are
accounted for rather than fixed: **seven are anonymous instances**, left so because #906 asked for
no code changes, and the eighth is `SheafOfModules.isFiniteType`, which carries
`@[inherit_doc SheafOfModules.IsFiniteType]` and so **is** documented in the environment even
though no `/-- … -/` precedes it here.

An anonymous instance *can* carry a docstring — the `/-- … -/` elaborates and the environment
keeps it — but there is no name to cite it by except the one Lean generates, which is why the
seven are described here instead. That is the same convention as `Oka/ComplexSpace.lean` and
`Oka/Algebra/Category/Grp/EpiMono.lean`.

`lake lint` was silent about all nineteen, and for three different reasons: `docBlame` exempts
**every** instance, named or anonymous, `docBlameThm` covers theorems and is off by default in
Batteries and not turned on here, and the one `abbrev` `docBlame` does reach inherits its
docstring. Turning `docBlameThm` on repository-wide would fire on every undocumented theorem
under `Oka/`; that count is taxis #928 and is a separate question.

## Main results

- `SheafOfModules.IsFiniteType.of_epi`
- `SheafOfModules.IsFiniteType.of_coversTop`
- `SheafOfModules.isFiniteType_pushforward`
- `SheafOfModules.GeneratingSections.restrict`
-/

@[expose] public section

universe w u v' u' v₂ u₂

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

section

variable [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Local generators data can be transported along a morphism `f : M ⟶ N` whose
restriction to every object remains an epimorphism. This applies in particular to
isomorphisms (see `SheafOfModules.IsFiniteType.of_iso`) and, when `C` has binary
products, to arbitrary epimorphisms (see `SheafOfModules.IsFiniteType.of_epi`). -/
@[simps]
noncomputable def LocalGeneratorsData.ofEpi {M N : SheafOfModules.{u} R}
    (σ : M.LocalGeneratorsData.{w}) (f : M ⟶ N) [∀ (X : C), Epi (f.over X)] :
    N.LocalGeneratorsData.{w} where
  I := σ.I
  X := σ.X
  coversTop := σ.coversTop
  generators i := (σ.generators i).ofEpi (f.over (σ.X i))

instance {M N : SheafOfModules.{u} R} (σ : M.LocalGeneratorsData.{w}) (f : M ⟶ N)
    [∀ (X : C), Epi (f.over X)] [σ.IsFiniteType] : (σ.ofEpi f).IsFiniteType where
  isFiniteType i :=
    haveI : (σ.generators i).IsFiniteType :=
      LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i
    inferInstanceAs ((σ.generators i).ofEpi (f.over (σ.X i))).IsFiniteType

/-- **Being of finite type passes to the target of a slicewise epimorphism.** This is the
primitive form of the statement: the hypothesis is that `f.over X` is an epimorphism for every
`X`, which is what `SheafOfModules.LocalGeneratorsData.ofEpi` consumes on each member of a
covering family. `SheafOfModules.IsFiniteType.of_epi` is the form to quote when only `Epi f`
is in hand. -/
lemma IsFiniteType.of_epi_over {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [∀ (X : C), Epi (f.over X)] [M.IsFiniteType] : N.IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨σ, _⟩ := IsFiniteType.exists_localGeneratorsData M
    exact ⟨σ.ofEpi f, inferInstance⟩

/-- Being of finite type transports along an isomorphism. -/
lemma IsFiniteType.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] :
    N.IsFiniteType :=
  haveI (X : C) : Epi (e.hom.over X) := inferInstance
  .of_epi_over e.hom

/-- The same at a morphism that happens to be invertible, so that a consumer holding an
`IsIso` instance need not build the `Iso` by hand. -/
lemma isFiniteType_of_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    [M.IsFiniteType] : N.IsFiniteType :=
  .of_iso (asIso f)

instance {M : SheafOfModules.{u} R} (σ : M.LocalGeneratorsData.{w}) [σ.IsFiniteType] :
    σ.shrink.IsFiniteType where
  isFiniteType i := LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i.2.choose

variable (R) in
@[inherit_doc IsFiniteType]
abbrev isFiniteType : ObjectProperty (SheafOfModules.{u} R) :=
  IsFiniteType

instance : (isFiniteType R).IsClosedUnderIsomorphisms where
  of_iso e h := letI := h; .of_iso e

/-- **A quotient of a sheaf of finite type is of finite type.** The usable form of
`SheafOfModules.IsFiniteType.of_epi_over`: with binary products on the site, `Epi f` already gives
`Epi (f.over X)` for every `X`, so the slicewise hypothesis is discharged by instance search. -/
lemma IsFiniteType.of_epi [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [Epi f] [M.IsFiniteType] : N.IsFiniteType :=
  haveI (X : C) : Epi (f.over X) := inferInstance
  .of_epi_over f

end

section map

variable [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {D : Type u₂} [Category.{v₂, u₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]

variable (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)

/-- The pushforward of `SheafOfModules.LocalGeneratorsData` along a continuous
and cocontinuous functor. This is the analogue for local generators data of
`SheafOfModules.QuasicoherentData.pushforward`. -/
@[simps I X]
noncomputable def LocalGeneratorsData.pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.LocalGeneratorsData) :
    LocalGeneratorsData ((pushforward φ).obj M) where
  I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
    refine K.superset_covering ?_ <| G.cover_lift K _ (P.coversTop (G.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  generators i :=
    letI G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
    letI ψ : S.over i.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1) (J.over (P.X i.2.1))).obj
          (R.over (P.X i.2.1)) :=
      ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
    letI overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      SheafOfModules.pushforward (𝟙 _)
    letI e : (SheafOfModules.pushforward ψ).obj (unit (R.over (P.X i.snd.fst))) ≅
      unit (S.over i.fst) := overS.mapIso η
    haveI : PreservesColimitsOfSize.{u, u, _} (SheafOfModules.pushforward ψ) := h _ _ _
    (P.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm

instance (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.LocalGeneratorsData) [P.IsFiniteType] :
    (P.pushforward G φ η h).IsFiniteType where
  isFiniteType i :=
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := P) i.2.1
    ⟨inferInstanceAs (Finite (P.generators i.2.1).I)⟩

/-- **Being of finite type survives a change of site.** Pushing forward along a continuous and
cocontinuous `G` preserves finite type, given an identification `η` of the pushed-forward unit
with the unit and the hypothesis `h` that pushforward along the sliced comparison map preserves
colimits. `SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint` discharges `h`, at the price
of four further hypotheses, and is the form to reach for first; `η` stays an explicit argument
there and every consumer in this file supplies it as an `Iso.refl`. -/
lemma isFiniteType_pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    IsFiniteType ((pushforward φ).obj M) := by
  obtain ⟨P, _⟩ := IsFiniteType.exists_localGeneratorsData M
  exact ⟨(P.pushforward G φ η h).shrink, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The sharp form of `SheafOfModules.isFiniteType_pushforward`**, and the one every consumer
here uses. When `G` is itself a left adjoint and `φ` is an isomorphism, the colimit-preservation
hypothesis of that lemma is not an assumption but a consequence: the sliced comparison map is
again an isomorphism, so pushforward along it is a left adjoint and preserves every colimit. -/
lemma isFiniteType_pushforward_of_isLeftAdjoint (η : (pushforward φ).obj (unit R) ≅ unit S)
    [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    IsFiniteType ((pushforward φ).obj M) := by
  apply +allowSynthFailures isFiniteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

end map

section bind

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Given a cover `X` and local generators data for `M` restricted to each `X i`, we may
glue them into local generators data for `M` itself. This is the analogue for local
generators data of `SheafOfModules.QuasicoherentData.bind`. -/
noncomputable def LocalGeneratorsData.bind {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, LocalGeneratorsData (M.over (X i))) :
    M.LocalGeneratorsData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i ↦ (D i).coversTop)
  generators i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    (((D i.1).generators i.2).map e.inverse (.refl _)).ofEpi
      (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over (X i.1)).over ((D i.1).X i.2)))).hom

instance {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, LocalGeneratorsData (M.over (X i)))
    [∀ i, (D i).IsFiniteType] : (LocalGeneratorsData.bind M X hX D).IsFiniteType where
  isFiniteType i :=
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := D i.1) i.2
    ⟨inferInstanceAs (Finite ((D i.1).generators i.2).I)⟩

/-- Being of finite type is local: if `M` restricts to a sheaf of finite type on
a cover of the terminal object, then `M` is of finite type. -/
lemma IsFiniteType.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, IsFiniteType (M.over (X i))] :
    M.IsFiniteType := by
  have h (i : I) := IsFiniteType.exists_localGeneratorsData (M.over (X i))
  choose D hD using h
  haveI := hD
  exact ⟨(LocalGeneratorsData.bind M X hX D).shrink, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction to a slice preserves finite type**, which is the direction opposite to
`SheafOfModules.IsFiniteType.of_coversTop`: that one glues finiteness over a covering family into
finiteness on the whole site, this one restricts finiteness to a single slice. It is
`SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint` at `Over.forget X`, where the
comparison map is the identity. -/
lemma IsFiniteType.over
    [HasPullbacks C] [HasBinaryProducts C] (M : SheafOfModules.{u} R) (X : C)
    [M.IsFiniteType] : IsFiniteType (M.over X) :=
  isFiniteType_pushforward_of_isLeftAdjoint _ _ (Iso.refl _)

/-- Variant of `SheafOfModules.IsFiniteType.of_coversTop` taking the finiteness of the
restrictions as an explicit hypothesis. -/
lemma IsFiniteType.of_coversTop_of_forall {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, IsFiniteType (R := R.over (X i)) (M.over (X i))) :
    M.IsFiniteType :=
  haveI := h
  .of_coversTop M X hX

end bind

section biprod

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The tautological generating sections of a free sheaf of modules. -/
noncomputable def freeGeneratingSections (I : Type u) :
    (free (R := R) I).GeneratingSections where
  I := I
  s := freeSection
  epi := by
    rw [show (freeSection : I → _) = (free (R := R) I).freeHomEquiv (𝟙 _) from rfl,
      Equiv.symm_apply_apply]
    infer_instance

instance (I : Type u) [Finite I] : (freeGeneratingSections (R := R) I).IsFiniteType :=
  ⟨inferInstanceAs (Finite I)⟩

/-- Generating sections of two sheaves of modules induce generating sections of their
binary biproduct. -/
noncomputable def GeneratingSections.biprod {A B : SheafOfModules.{u} R}
    (σA : A.GeneratingSections) (σB : B.GeneratingSections) :
    (A ⊞ B).GeneratingSections where
  I := σA.I ⊕ σB.I
  s := (A ⊞ B).freeHomEquiv
    ((freeSumIso σA.I σB.I).inv ≫ coprod.map σA.π σB.π ≫ (biprod.isoCoprod A B).inv)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

instance {A B : SheafOfModules.{u} R} (σA : A.GeneratingSections) (σB : B.GeneratingSections)
    [σA.IsFiniteType] [σB.IsFiniteType] : (σA.biprod σB).IsFiniteType :=
  ⟨inferInstanceAs (Finite (σA.I ⊕ σB.I))⟩

end biprod

section ofGeneratingSections

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C]

/-- A sheaf of modules admitting finitely many global generating sections is
of finite type. -/
lemma IsFiniteType.of_generatingSections {M : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) [σ.IsFiniteType] : M.IsFiniteType where
  exists_localGeneratorsData :=
    ⟨σ.localGeneratorsData, ⟨fun _ ↦ ⟨inferInstanceAs (Finite σ.I)⟩⟩⟩

end ofGeneratingSections

section freeBiprod

variable {C : Type u} [SmallCategory C] [HasPullbacks C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Auxiliary statement for `SheafOfModules.isFiniteType_free_biprod`: over an object on which
`M` is generated by finitely many sections, so is its biproduct with a finite free sheaf. -/
lemma isFiniteType_over_free_biprod {I : Type u} [Finite I] (M : SheafOfModules.{u} R) {X : C}
    (σ : (M.over X).GeneratingSections) [σ.IsFiniteType] :
    IsFiniteType (R := R.over X) ((free (R := R) I ⊞ M).over X) := by
  haveI : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : IsFiniteType (R := R.over X) ((free (R := R.over X) I) ⊞ (M.over X)) :=
    IsFiniteType.of_generatingSections (M := (free (R := R.over X) I) ⊞ (M.over X))
      ((freeGeneratingSections I).biprod σ)
  exact IsFiniteType.of_iso (M := (free (R := R.over X) I) ⊞ (M.over X))
    (biprod.mapIso (overFreeIso I X) (Iso.refl _) ≪≫ (overBiprodIso (free (R := R) I) M X).symm)

/-- **The biproduct of a finite free sheaf of modules with a sheaf of finite type is of finite
type.**

A free sheaf is generated by its tautological sections *globally*, so only one cover is
involved: the one on which `M` is generated. -/
lemma isFiniteType_free_biprod {I : Type u} [Finite I] (M : SheafOfModules.{u} R)
    [M.IsFiniteType] : (free (R := R) I ⊞ M).IsFiniteType := by
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData M
  refine IsFiniteType.of_coversTop_of_forall (free (R := R) I ⊞ M) σ.X σ.coversTop (fun i ↦ ?_)
  haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i
  exact isFiniteType_over_free_biprod M (σ.generators i)

end freeBiprod

section overOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- Being of finite type is carried across the iterated slice equivalence, from
`R.over Y.left` to `(R.over X).over Y`. -/
lemma isFiniteType_overOverEquivalence_functor_obj {X : C} {Y : Over X}
    (M' : SheafOfModules.{u} (R.over Y.left)) [M'.IsFiniteType] :
    IsFiniteType (R := (R.over X).over Y) ((overOverEquivalence X Y).functor.obj M') := by
  exact isFiniteType_pushforward_of_isLeftAdjoint (Over.iteratedSliceEquiv Y).functor (𝟙 _)
    (by exact Iso.refl _)

/-- The same in the other direction, from `(R.over X).over Y` to `R.over Y.left`. -/
lemma isFiniteType_overOverEquivalence_inverse_obj {X : C} {Y : Over X}
    (N' : SheafOfModules.{u} ((R.over X).over Y)) [N'.IsFiniteType] :
    IsFiniteType (R := R.over Y.left) ((overOverEquivalence X Y).inverse.obj N') := by
  exact isFiniteType_pushforward_of_isLeftAdjoint (Over.iteratedSliceEquiv Y).inverse (𝟙 _)
    (by exact Iso.refl _)

/-- The converse of `SheafOfModules.isFiniteType_overOverEquivalence_functor_obj`: if the image
is of finite type then so was the sheaf. Proved from the other direction of the equivalence
together with its unit isomorphism, not by a separate argument. -/
lemma IsFiniteType.of_overOverEquivalence_functor_obj {X : C} {Y : Over X}
    {M' : SheafOfModules.{u} (R.over Y.left)}
    (h : IsFiniteType (R := (R.over X).over Y) ((overOverEquivalence X Y).functor.obj M')) :
    M'.IsFiniteType :=
  haveI := h
  haveI : IsFiniteType (R := R.over Y.left)
      ((overOverEquivalence (R := R) X Y).inverse.obj
        ((overOverEquivalence (R := R) X Y).functor.obj M')) :=
    isFiniteType_overOverEquivalence_inverse_obj _
  IsFiniteType.of_iso (M := (overOverEquivalence (R := R) X Y).inverse.obj
      ((overOverEquivalence (R := R) X Y).functor.obj M'))
    ((overOverEquivalence (R := R) X Y).unitIso.symm.app M')

/-- The converse of `SheafOfModules.isFiniteType_overOverEquivalence_inverse_obj`, by the same
argument through the counit isomorphism. -/
lemma IsFiniteType.of_overOverEquivalence_inverse_obj {X : C} {Y : Over X}
    {N' : SheafOfModules.{u} ((R.over X).over Y)}
    (h : IsFiniteType (R := R.over Y.left) ((overOverEquivalence X Y).inverse.obj N')) :
    N'.IsFiniteType :=
  haveI := h
  haveI : IsFiniteType (R := (R.over X).over Y)
      ((overOverEquivalence (R := R) X Y).functor.obj
        ((overOverEquivalence (R := R) X Y).inverse.obj N')) :=
    isFiniteType_overOverEquivalence_functor_obj _
  IsFiniteType.of_iso (M := (overOverEquivalence (R := R) X Y).functor.obj
      ((overOverEquivalence (R := R) X Y).inverse.obj N'))
    ((overOverEquivalence (R := R) X Y).counitIso.app N')

end overOver

section restrict

variable [HasPullbacks C] [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Generating sections restrict along a morphism of the site.**

If `M` is generated over `Y` by a family of sections, it is generated over any `X` lying over
`Y` by their restrictions. This is the operation an argument that refines a covering needs:
`SheafOfModules.IsFiniteType` hands out generators over the members of *some* covering, and a
caller which wants them over a covering of its own choosing has to move them.

The two functors that do it are Mathlib's. `SheafOfModules.overMap` is the pushforward along
`CategoryTheory.Over.map f`, a left adjoint when `C` has pullbacks and therefore colimit
preserving, so `SheafOfModules.GeneratingSections.map` applies to it; and
`SheafOfModules.overFunctorMap` says that restricting to `Over Y` and then extending to `Over X`
is restricting to `Over X`, so `SheafOfModules.GeneratingSections.ofEpi` along its component
lands where it should. Nothing here is specific to a topological site.

**`HasPullbacks C` is the load-bearing hypothesis**: without it `SheafOfModules.overMap` is not
known to be a left adjoint, so it is not known to preserve colimits and
`SheafOfModules.GeneratingSections.map` does not apply.

It is **not** the only hypothesis beyond the ones `SheafOfModules.IsFiniteType` carries.
That class asks for `HasWeakSheafify` on the slice sites and this needs the stronger
`HasSheafify`; re-declaring the definition under `IsFiniteType`'s hypotheses plus
`HasPullbacks C` fails with `failed to synthesize HasSheafify (J.over X) AddCommGrpCat`. -/
noncomputable def GeneratingSections.restrict {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (σ : (M.over Y).GeneratingSections) : (M.over X).GeneratingSections :=
  (σ.map (overMap R f) (overMapUnitIso f).symm).ofEpi (((overFunctorMap R f).app M).hom)

/-- **Restriction preserves finiteness of a family of generating sections**, because neither
`SheafOfModules.GeneratingSections.map` nor `SheafOfModules.GeneratingSections.ofEpi` changes the
index type. `unfold` is needed: `SheafOfModules.GeneratingSections.restrict` is an ordinary
definition, so instance search does not see the two constructions it is built from. -/
instance GeneratingSections.isFiniteType_restrict {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (σ : (M.over Y).GeneratingSections) [σ.IsFiniteType] : (σ.restrict f).IsFiniteType := by
  unfold GeneratingSections.restrict
  infer_instance

end restrict

end SheafOfModules
