/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Restricting a sheaf of modules to a slice: free sheaves, biproducts, kernels, iterated slices

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`; see
`README.md` on the mirror tree.

**That path is not free, and the number is worth stating.** The target imports none of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` or
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`, and the declarations below need all
three: biproducts and kernels from the first, `SheafOfModules.free` from the second,
`SheafOfModules.pushforwardPushforwardEquivalence` from the third. Measured, the three together
add **103** files to the target's own transitive closure, which is **1473** files. The baseline is
the target's closure and not this file's, so 103 is the marginal cost of the three named imports
and not the total cost of upstreaming the content. That is **larger than anything else this
development has priced** — `README.md` records 96 files as the cost that once forced a declaration
into a different mirror file, and this is past it — and it is recorded here rather than acted on,
because splitting the file by destination is a decision about Mathlib's layout and not a
documentation change. The three alternative destinations are the three files just named.

**How the number was taken, because the obvious instrument gets it wrong.** Breadth-first search
over `^(public )?import` in `.lake/packages/mathlib`, **with comments masked first**. Fourteen
files of Mathlib carry a line beginning `import …` inside a comment — 29 such lines, two of them
a bare `import Mathlib` — and an unmasked search follows them. The one that reaches this closure is
`Mathlib/Tactic/FunProp.lean`, whose documentation shows
`import Mathlib.Analysis.Complex.Trigonometric` in an example; that single phantom edge takes this
baseline from 1473 to 1744 — **271** modules, of which only **8** are under `Mathlib/Analysis/`, the
rest being the algebra, topology and order substrate that one analysis module sits on. What it adds
is a fact about the baseline and not about the edge: against a closure that already reaches complex
analysis it adds nothing. Two further phantom edges, in `Mathlib/Tactic/ExtractGoal.lean` and
`Mathlib/Tactic/MinImports.lean`, account for the remaining three of the 274 modules this closure
inflates by when nothing is masked. The phantom modules land on *both* sides of the subtraction, so
they deflate the marginal cost as well: unmasked, this paragraph read 75 against 1747, and the
instrument that produced those figures had been validated on the two figures already in the tree —
2 for `Mathlib.RingTheory.Localization.Finiteness` into
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` and
3 for `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` into
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` — which **both reproduce on the broken instrument**,
because neither of those targets reaches a comment-embedded import. Two agreeing deltas in one
corner of the library are not a test of a closure computation; a fixture whose docstring contains
`import Mathlib` is.

`SheafOfModules.overFunctor R X` restricts a sheaf of modules to the slice `Over X`. Mathlib
builds it, as a `SheafOfModules.pushforward` along an identity, and knows it is a left adjoint;
what is here is what it does to the constructions this development uses.

* `SheafOfModules.overFreeIso` — the restriction of a free sheaf is free on the same index type.
* `SheafOfModules.overBiprodIso` — restriction commutes with binary biproducts, because it is a
  left adjoint and in an additive category the binary coproduct is the biproduct.
* `SheafOfModules.overKernelIso` — restriction commutes with kernels. This one needs the *right*
  adjoint, which is the second of the two anonymous instances below and is stated over a small
  site; the first anonymous instance is the left adjoint, which is not.
* `SheafOfModules.overOverEquivalence` and its four compatibility isomorphisms — sheaves of
  modules on `Over Y.left` are the same as sheaves of modules on `(R.over X).over Y`, which is
  `CategoryTheory.Over.iteratedSliceEquiv` carried up to modules. Three of the four compatibility
  isomorphisms are `Iso.refl`, and their proofs say so; they exist because the two sides are not
  syntactically equal and a consumer needs a term rather than a defeq it has to find.

The site hypotheses differ between these groups, which is why the `variable` blocks below are not
shared: the kernel statement wants a small site, the biproduct statement wants sheafification on
every slice, and `SheafOfModules.overOverEquivalence` wants neither.

This file's only consumer is `Oka/Algebra/Category/ModuleCat/Sheaf/Generators.lean`.

## Main definitions

- `SheafOfModules.overFreeIso`, `SheafOfModules.overBiprodIso`, `SheafOfModules.overKernelIso`
- `SheafOfModules.overOverEquivalence`
-/

@[expose] public section

universe w v' u' u

open CategoryTheory Limits

namespace SheafOfModules

section

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

instance (X : C) : (overFunctor.{w} R X).IsLeftAdjoint :=
  inferInstanceAs (pushforward.{w} (𝟙 (R.over X))).IsLeftAdjoint

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The restriction of a free sheaf of modules to `Over X` is free. -/
noncomputable def overFreeIso (I : Type u) (X : C) :
    free (R := R.over X) I ≅ (free (R := R) I).over X :=
  mapFreeIso (overFunctor R X) I (Iso.refl _)

end

section

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction to `Over X` commutes with binary biproducts.**

Restriction is a left adjoint (`SheafOfModules.overFunctor`), so it preserves the coproduct;
in an additive category the coproduct is the biproduct. -/
noncomputable def overBiprodIso (M N : SheafOfModules.{u} R) (X : C) :
    (M ⊞ N).over X ≅ (M.over X) ⊞ (N.over X) :=
  (overFunctor R X).mapIso (biprod.isoCoprod M N) ≪≫
    (PreservesColimitPair.iso (overFunctor R X) M N).symm ≪≫ (biprod.isoCoprod _ _).symm

end

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Sheaves of modules over `R.over Y.left` are equivalent to sheaves of modules over
`(R.over X).over Y`. -/
noncomputable def overOverEquivalence (X : C) (Y : Over X) :
    SheafOfModules.{u} (R.over Y.left) ≌ SheafOfModules.{u} ((R.over X).over Y) :=
  pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Y)
    (S := (R.over X).over Y) (R := R.over Y.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)

/-- The equivalence `overOverEquivalence` is compatible with restriction. -/
noncomputable def overOverEquivalenceObjIso (M : SheafOfModules.{u} R) (X : C) (Y : Over X) :
    (overOverEquivalence (R := R) X Y).functor.obj (M.over Y.left) ≅ (M.over X).over Y := by
  exact Iso.refl _

/-- The equivalence `overOverEquivalence` sends the unit to the unit. -/
noncomputable def overOverEquivalenceUnitIso (X : C) (Y : Over X) :
    (overOverEquivalence (R := R) X Y).functor.obj (unit (R.over Y.left)) ≅
      unit ((R.over X).over Y) := by
  exact Iso.refl _

/-- The inverse of the equivalence `overOverEquivalence` sends the unit to the unit. -/
noncomputable def overOverEquivalenceInverseUnitIso (X : C) (Y : Over X) :
    unit (R.over Y.left) ≅
      (overOverEquivalence (R := R) X Y).inverse.obj (unit ((R.over X).over Y)) := by
  exact Iso.refl _

/-- The inverse of the equivalence `overOverEquivalence` is compatible with restriction. -/
noncomputable def overOverEquivalenceInverseObjIso (M : SheafOfModules.{u} R) (X : C)
    (Y : Over X) :
    (overOverEquivalence (R := R) X Y).inverse.obj ((M.over X).over Y) ≅ M.over Y.left := by
  exact ((overOverEquivalence (R := R) X Y).unitIso.app (M.over Y.left)).symm

end

section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

instance (X : C) : (overFunctor.{u} R X).IsRightAdjoint := by
  let φ : R.over X ⟶ R.over X := 𝟙 (R.over X)
  haveI : (PresheafOfModules.pushforward.{u} (F := Over.forget X) (R := R.obj)
      (S := (R.over X).obj) φ.hom).IsRightAdjoint :=
    CategoryTheory.Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top (F := Over.forget X) (R := R.obj)
        (S := (R.over X).obj) φ.hom)
  exact (PullbackConstruction.adjunction.{u} (F := Over.forget X) (R := R) φ).isRightAdjoint

variable [HasSheafify J AddCommGrpCat.{u}] [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The restriction functor to `Over X` commutes with kernels. -/
noncomputable def overKernelIso {M N : SheafOfModules.{u} R} (φ : M ⟶ N) (X : C) :
    (kernel φ).over X ≅ kernel (φ.over X) :=
  PreservesKernel.iso (overFunctor R X) φ

end

end SheafOfModules
