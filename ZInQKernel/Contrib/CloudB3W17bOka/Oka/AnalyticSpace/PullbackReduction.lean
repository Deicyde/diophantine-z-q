/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.CutOutFibreProduct
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.PullbackLimit

/-!
# The reduction of a general cospan, and `HasPullbacks ComplexAnalytic.AnalyticSpace`

`Oka/AnalyticSpace/PullbackLimit.lean` proves
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover`: a cospan `f : X ⟶ Z`,
`g : Y ⟶ Z` has a fibre product as soon as `X` is covered by opens `Uᵢ` along which the base
change of `g` is already known. **Nothing produced such a family for a general cospan, and this
file is what produces one.** With it,
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` synthesises.

## The route, and where it leaves Mathlib's

Mathlib does the same reduction for schemes in six declarations,
`Mathlib/AlgebraicGeometry/Pullbacks.lean`'s `AlgebraicGeometry.Scheme.Pullback.affine_hasPullback`
through the instance `CategoryTheory.Limits.HasPullbacks AlgebraicGeometry.Scheme`. The first four
steps are the same here: a cospan of local models, then one of them replaced by an arbitrary
space, then the second, then a general cospan covered by the preimages of charts of the base.

**Two things are different and both are visible in the statements below.**

* **A chart is an equality here and an open immersion there.**
  `ComplexAnalytic.exists_restrict_eq_ofCutOut` gives `X.restrict U = AnalyticSpace.ofCutOut hcut`
  — an `Eq` of analytic spaces, not an isomorphism — so a local model can be substituted for the
  open subspace it presents rather than transported across an equivalence. That is what
  `ComplexAnalytic.IsCutOutModel` packages, and it is why the base case here is
  `ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel`, a transport of
  `ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` along three such equalities, where Mathlib
  needs no transport at all: `Spec A` is affine on the nose. **The substitution is the reason
  every hypothesis below is stated of an object and not of a morphism** — `subst` needs a free
  variable on one side of the equation, which is what an object of the cospan is and what
  `X.restrict U` is not.
* **The last cover is by opens and not by pullbacks.**
  `ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` asks for a family of
  `ComplexAnalytic.AnalyticSpace.Opens`, where Mathlib's asks for a family of open immersions, so
  the analytic family is `f ⁻¹' Wₖ` for `Wₖ` the charts of `Z` — with no pullback object named.
  **`CategoryTheory.Limits.hasPullback_assoc_symm` is therefore not used**, and neither is
  `CategoryTheory.Limits.hasPullback_symmetry` at that step, although the second is used twice at
  the step before it, exactly as Mathlib uses it. What replaces the associativity argument is one
  pasting: `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` is the square that says
  restricting over an open of the target is a base change, and
  `CategoryTheory.IsPullback.paste_horiz` glues the fibre product over the chart onto it.
  `ComplexAnalytic.AnalyticSpace.restrictHom_fac` is what turns the pasted square's bottom edge
  back into `X.ofRestrict (f ⁻¹' W) ≫ f`, which is the edge
  `…Pullback.hasPullback_of_cover` asks about.

## Main results

- `ComplexAnalytic.IsCutOutModel`: **an analytic space *is* a local model**, on the nose — the
  conclusion of `ComplexAnalytic.exists_restrict_eq_ofCutOut` read as a predicate on a space.
- `ComplexAnalytic.exists_isCutOutModel_restrict`: **every point has an open neighbourhood whose
  open subspace is one**.
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel`: **a cospan of local models has a
  fibre product**, which is `ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` with the three
  presentations substituted in.
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_right`: **the source of the first
  leg may be arbitrary**, by covering it.
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_base`: **only the base need be a
  local model**, by covering the source of the second leg and two symmetries.
- `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp`: **the
  covering family a general cospan needs**, one member at a time.
- `ComplexAnalytic.AnalyticSpace.hasPullback`: **every cospan of complex analytic spaces has a
  fibre product.**
- `ComplexAnalytic.AnalyticSpace.hasPullbacks`: **the category has pullbacks.**

**`ComplexAnalytic.AnalyticSpace.hasPullback` and `…hasPullbacks` are named**, where Mathlib's
corresponding two are anonymous instances, so every declaration of this file carries a
`#print axioms` guard under its own name.

## What this does not do

* **It says nothing about the *points* of a fibre product.** No declaration here identifies the
  carrier of `CategoryTheory.Limits.pullback f g` with a set of pairs, and none of the four steps
  needs such an identification: the limit is glued and the gluing is compared to nothing.
* **It does not base-change a class of morphisms along a general square.**
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` of `CategoryTheory.Limits.pullback.snd f g` is a
  statement about the class and does not follow from the fibre product existing;
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` carries it across the square it builds itself and
  the general statement stays owed.
* **It states no `CategoryTheory.IsPullback` for a general cospan**, only
  `CategoryTheory.Limits.HasPullback`, and so keeps no identification of the limit with the object
  presenting it. `ComplexAnalytic.AnalyticSpace.fibreProdCutOutIsoPullback` is that identification
  for a cospan of local models and there is no analogue here.
* **It gives no fibre product in the category of covers.**
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` are `CategoryTheory.MorphismProperty.Over`
  categories and a limit in one of them is not a limit in `ComplexAnalytic.AnalyticSpace`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace ComplexAnalytic

/-- **A complex analytic space is a *local model on the nose* if it is `ofCutOut` of some cut-out
datum** — not merely isomorphic to one.

This is the conclusion of `ComplexAnalytic.exists_restrict_eq_ofCutOut` read as a predicate, and
the equality is the point: `Oka/AnalyticSpace/PullbackReduction.lean`'s reduction substitutes the
presentation for the space with `subst`, which asks for an `Eq` and not an
`CategoryTheory.Iso`, and asks further that one side be a free variable — which is why this is a
predicate on a *space* rather than a hypothesis on a chart.

**It is stated in the `ComplexAnalytic` namespace and not in `ComplexAnalytic.AnalyticSpace`**,
for the reason `ComplexAnalytic.exists_restrict_eq_ofCutOut` gives: inside a declaration whose
name begins `AnalyticSpace.` the tokens `complexAffineSpace` and `Opens` resolve to
`ComplexAnalytic.AnalyticSpace.complexAffineSpace` and `ComplexAnalytic.AnalyticSpace.Opens`
rather than to the locally ringed space and to `TopologicalSpace.Opens`, and the statement below
would then be about a different `ℂ^n`.

**It is not `ComplexAnalytic.IsLocalModel`**, which is a predicate on a
`AlgebraicGeometry.LocallyRingedSpace` asserting the existence of a closed immersion out of *that
space*; this one asserts an equality of analytic spaces, so it carries the `ℂ`-algebra structure
`ComplexAnalytic.AnalyticSpace.ofCutOut` builds along with it. -/
def IsCutOutModel (S : AnalyticSpace.{u}) : Prop :=
  ∃ (n k : ℕ) (V : Opens (complexAffineSpace.{u} n)) (M : LocallyRingedSpace.{u})
    (i : M ⟶ (complexAffineSpace.{u} n).restrict V.isOpenEmbedding)
    (f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤))
    (hcut : IsCutOutBy i f), S = AnalyticSpace.ofCutOut hcut

/-- **Every point of a complex analytic space has an open neighbourhood whose open subspace is a
local model on the nose.**

`ComplexAnalytic.exists_restrict_eq_ofCutOut` with its last six binders folded into
`ComplexAnalytic.IsCutOutModel`. The fold is what makes the neighbourhood choosable: the
reduction below picks one at every point with `choose`, and a `choose` over the unfolded
statement would carry the ambient dimension, the number of equations and the chart map into every
later goal. -/
theorem exists_isCutOutModel_restrict (X : AnalyticSpace.{u}) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsCutOutModel (X.restrict U) := by
  obtain ⟨U, hxU, n, k, V, i, f, hcut, h⟩ := exists_restrict_eq_ofCutOut X x
  exact ⟨U, hxU, n, k, V, _, i, f, hcut, h⟩

namespace AnalyticSpace

variable {X Y Z : AnalyticSpace.{u}}

/-! ### The base case, and the two covers that widen it -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **A cospan of local models has a fibre product** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.affine_hasPullback`, over `ComplexAnalytic.AnalyticSpace`.

`ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` already says this of a cospan whose three
objects are literally `ComplexAnalytic.AnalyticSpace.ofCutOut`; **the work here is the three
substitutions that put an arbitrary cospan into that shape**, and they are `subst` and not a
transport because `ComplexAnalytic.IsCutOutModel` carries an equality of spaces. Mathlib needs no
counterpart, `AlgebraicGeometry.Scheme.Spec`'s image being affine definitionally. -/
theorem hasPullback_of_isCutOutModel (hX : IsCutOutModel X) (hY : IsCutOutModel Y)
    (hZ : IsCutOutModel Z) (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := hX
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := hY
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := hZ
  infer_instance

/-- **The source of the first leg may be an arbitrary complex analytic space** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback`.

`ComplexAnalytic.exists_isCutOutModel_restrict` at every point of `X` gives a covering family of
opens whose open subspaces are local models, and
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` at that family reduces the cospan to
`ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel` on each member.

**The family is indexed by the points of `X` and that is the cheapest legal choice.**
`…Pullback.hasPullback_of_cover` fixes the index type in `Type u`, which is the universe the
carrier of `X : ComplexAnalytic.AnalyticSpace.{u}` lives in; an index type built from `X.Opens` or
from a `Sigma` would have to be placed there by hand, and covering `X` by one open per point costs
nothing since the family is not asked to be locally finite or injective. -/
theorem hasPullback_of_isCutOutModel_right (hY : IsCutOutModel Y) (hZ : IsCutOutModel Z)
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := by
  choose U hxU hmod using fun x : X ↦ exists_isCutOutModel_restrict X x
  haveI (x : X) : HasPullback (X.ofRestrict (U x) ≫ f) g :=
    hasPullback_of_isCutOutModel (hmod x) hY hZ _ g
  exact Pullback.hasPullback_of_cover U f g fun x ↦ ⟨x, hxU x⟩

/-- **Only the base of the cospan need be a local model** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.base_affine_hasPullback`, and the same two symmetries.

The cover is of `Y` this time, so
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` is applied to the cospan the other
way round and `CategoryTheory.Limits.hasPullback_symmetry` transposes it back — once inside, to
put each member's statement into the orientation
`ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_right` proves, and once outside. **The
two symmetries are not a pair that cancels**: the inner one is applied under a binder over the
members of the cover and the outer one to the assembled statement. -/
theorem hasPullback_of_isCutOutModel_base (hZ : IsCutOutModel Z) (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g := by
  choose V hyV hmod using fun y : Y ↦ exists_isCutOutModel_restrict Y y
  haveI (y : Y) : HasPullback (Y.ofRestrict (V y) ≫ g) f := by
    haveI : HasPullback f (Y.ofRestrict (V y) ≫ g) :=
      hasPullback_of_isCutOutModel_right (hmod y) hZ f _
    exact hasPullback_symmetry _ _
  haveI : HasPullback g f := Pullback.hasPullback_of_cover V g f fun y ↦ ⟨y, hyV y⟩
  exact hasPullback_symmetry _ _

/-! ### The covering family a general cospan needs, and the category with pullbacks -/

/-- **The base change of `g` exists along the inclusion of the preimage of a chart of the base** —
Mathlib's `AlgebraicGeometry.Scheme.Pullback.left_affine_comp_pullback_hasPullback`, and the one
step whose analytic form is not Mathlib's.

Mathlib covers `X` by the schemes `X ×_Z Z_k` and reassociates with
`CategoryTheory.Limits.hasPullback_assoc_symm`. Here the cover is by the *opens* `f ⁻¹' W`, since
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` asks for a family of
`ComplexAnalytic.AnalyticSpace.Opens`, and there is no pullback object to reassociate. **What
takes its place is one horizontal pasting of two squares**:

* the right-hand square is `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` at `g` and `W`,
  which says `Y|g ⁻¹' W` is the base change of `g` along the inclusion of `W`;
* the left-hand square is the fibre product of `ComplexAnalytic.AnalyticSpace.restrictHom f W`
  and `…restrictHom g W` over `Z|W`, which exists by
  `ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_base` because `Z|W` is a local model
  and the two other objects are arbitrary — this is the only place the hypothesis is used;
* `CategoryTheory.IsPullback.paste_horiz` makes the outer rectangle a pullback square, and
  `ComplexAnalytic.AnalyticSpace.restrictHom_fac` rewrites its bottom edge
  `restrictHom f W ≫ Z.ofRestrict W` into `X.ofRestrict (f ⁻¹' W) ≫ f`, which is the edge the
  statement is about.

**The rewrite is the whole of the difference between the two edges**, and it is an equation
between two morphisms out of the same open subspace rather than an isomorphism of objects, so
nothing has to be transported afterwards. -/
theorem hasPullback_ofRestrict_comp {W : Z.Opens}
    (hW : IsCutOutModel (Z.restrict W)) (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback (X.ofRestrict ((Opens.map f.toLRSHom.base).obj W) ≫ f) g := by
  haveI : HasPullback (restrictHom g W) (restrictHom f W) :=
    hasPullback_of_isCutOutModel_base hW _ _
  have h := ((IsPullback.of_hasPullback (restrictHom g W) (restrictHom f W)).paste_horiz
    (isPullback_ofRestrict g W)).flip
  rw [restrictHom_fac] at h
  exact h.hasPullback

/-- **Every cospan of complex analytic spaces has a fibre product.**

`ComplexAnalytic.exists_isCutOutModel_restrict` at every point of `Z` gives a family of charts
`W z` of the *base*; their preimages under `f` are a family of
`ComplexAnalytic.AnalyticSpace.Opens` of `X` which covers `X`, because a point `x` lies in the
preimage of the chart chosen at `f x`. Each member's hypothesis is
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp` and
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` assembles them.

**This is where the cover finally comes from the base and not from either source**, which is why
it comes after the other two: `ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel_right`
covers `X` and `…hasPullback_of_isCutOutModel_base` covers `Y`, and neither can reduce the target,
so the target is what the chart family must be taken in. -/
instance hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := by
  choose W hzW hmod using fun z : Z ↦ exists_isCutOutModel_restrict Z z
  haveI (z : Z) :
      HasPullback (X.ofRestrict ((Opens.map f.toLRSHom.base).obj (W z)) ≫ f) g :=
    hasPullback_ofRestrict_comp (hmod z) f g
  exact Pullback.hasPullback_of_cover (fun z ↦ (Opens.map f.toLRSHom.base).obj (W z)) f g
    fun x ↦ ⟨f.toLRSHom.base x, hzW _⟩

/-- **The category of complex analytic spaces has pullbacks** —
`CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan` at
`ComplexAnalytic.AnalyticSpace.hasPullback`, which is the whole proof.

**It is named where Mathlib's `CategoryTheory.Limits.HasPullbacks AlgebraicGeometry.Scheme` is
anonymous.** A `#print axioms` guard is by name, and the guard on this one is what records that
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` is a theorem of this
repository rather than a synthesis that happens to succeed at some call site. -/
instance hasPullbacks : HasPullbacks AnalyticSpace.{u} :=
  hasPullbacks_of_hasLimit_cospan _

end AnalyticSpace

end ComplexAnalytic
