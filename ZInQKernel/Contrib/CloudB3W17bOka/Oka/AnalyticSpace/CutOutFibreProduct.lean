/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.CutOutProduct
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.ZeroLocus

/-!
# The fibre product of two local models over a third

`Oka/AnalyticSpace/CutOutProduct.lean` makes the zero locus of the appended family
`ComplexAnalytic.AnalyticSpace.prodCutFamily` the binary product of two local models. This file
cuts that product down once more: given `a : X ⟶ S` and `b : Y ⟶ S` between local models presented
by cut-out data, **the zero locus inside `X × Y` of the `p` differences of the two composites to
`ℂ^p` is the fibre product `X ×_S Y`**, and `CategoryTheory.Limits.HasPullback a b` follows.

This is the first `CategoryTheory.Limits.HasPullback` instance in this repository over a cospan
**neither of whose legs is the inclusion of an open subspace and neither of which is finite
étale** — the two shapes `Oka/AnalyticSpace/PullbackOpen.lean` and
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` supply. **The second shape read *is finite étale
with Hausdorff source* until 2026-09-14**, when the separation axiom came out of that file; the
sentence is about which shapes the two files supply and the cospan here is a leg of neither, at
the wider shape as at the narrower. `Oka/AnalyticSpace/Finite.lean` and
`Oka/AnalyticSpace/LocalIso.lean` each carried a clause recording the absence of a third shape and
both are narrowed by this file; they are what a sweep for the phrase *cospan neither of whose
legs* over every tracked `.lean` and `.md` at `c00e2a1`, the commit this file is added on, read as
one whitespace-normalised string per file, returns besides
`Oka/AnalyticSpace/PullbackOpen.lean`'s own — which is about the diagonal and is bounded to that
file by the word *here* — and `Oka/AnalyticSpace/LocalIso.lean`'s own dated record of the wording
it retired earlier the same day.

## Why the cutting family is a family on the product and not on its ambient

`ComplexAnalytic.AnalyticSpace.prodCutFamily`'s two blocks are **pullbacks of sections of the
ambient** `ℂ^(n+m)|affineProdOpens V W` along the two ambient legs, which is why
`ComplexAnalytic.AnalyticSpace.ofCutOut` accepts them and why that product cost no analysis. The
`p` differences here are not of that shape: `a` and `b` are morphisms *out of the two subspaces*,
so their coordinate pullbacks are sections of `ComplexAnalytic.AnalyticSpace.prodCutOut` itself,
and a global section of a local model need not extend to the `ℂ^n|V` that model is cut out in.
This is the gap `Oka/AnalyticSpace/CutOutCompose.lean`'s header records, and what closes it is
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` — the zero locus of finitely many global
sections of an *arbitrary* analytic space, which is `Oka/AnalyticSpace/ZeroLocus.lean`'s subject.
**So this file cuts down with the general zero locus and not with
`ComplexAnalytic.AnalyticSpace.ofCutOut`**, and the object it produces is not presented as a local
model by anything below.

## The mapping property of the zero locus is here, and its placement is forced

`Oka/AnalyticSpace/ZeroLocus.lean`'s `## What is not here` says in terms that it composes no
mapping property for `ComplexAnalytic.AnalyticSpace.zeroLocusSubspace`, and names the recipe:
`ComplexAnalytic.IsCutOutBy.lift`, `ComplexAnalytic.IsCutOutBy.isCLinearHom_lift`, and the
faithfulness of `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` for uniqueness.
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift` below is that recipe run.

**It could not have been stated in that file**, and this is measured rather than asserted:
`Oka.AnalyticSpace.Factorisation`, where `ComplexAnalytic.IsCutOutBy.lift` and
`ComplexAnalytic.IsCutOutBy.isCLinearHom_lift` are declared, is **not** in
`Oka.AnalyticSpace.ZeroLocus`'s import closure — walked through `scripts/import_cost.py`'s
`IMPORT` pattern over its nesting-aware `strip_comments`, `Oka`-prefixed edges, transitively
closed. A scratch importing `Oka.AnalyticSpace.ZeroLocus` alone reports
`Unknown constant 'ComplexAnalytic.IsCutOutBy.lift'`. This is the same shape as the placement of
`ComplexAnalytic.AnalyticSpace.liftHom`, which `Oka/AnalyticSpace/CutOutProduct.lean` explains at
its own head: a mapping property lands with the first file that can state it.

`ComplexAnalytic.AnalyticSpace.hom_ext_restrict_complexAffineSpace` is a different case and its
placement **is** a preference, said so rather than left implicit. It mentions no product, no zero
locus and no fibre product, and `Oka/AnalyticSpace/HomToComplex.lean` — where
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` lives — reaches
`ComplexAnalytic.AnalyticSpace.ofRestrict` and `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`
through `Oka.AnalyticSpace.OpenSubspace`, which is in its import closure, so that file could hold
it with its body unchanged. It is here because it arrives with its only consumer, and moving it is
a one-declaration move a later push can make.

## The route

Write `X` and `Y` for the two local models and `S` for the base, all three
`ComplexAnalytic.AnalyticSpace.ofCutOut` of a cut-out datum, and `P` for
`ComplexAnalytic.AnalyticSpace.prodCutOut` of the two cutting families.

1. **The two composites to `ℂ^p`.** `ComplexAnalytic.AnalyticSpace.toAffineOfCutOut` is the
   immersion of `S` into `ℂ^p|U` followed by the inclusion of that open subspace, so that the two
   composites `P ⟶ ℂ^p` land in the *whole* affine space and their coordinate pullbacks are
   pullbacks of `ComplexAnalytic.coord`. Composing with the inclusion rather than stopping at
   `ℂ^p|U` is what lets step 4 be `ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace`.
2. **The cutting family.** `ComplexAnalytic.AnalyticSpace.eqCutFamily` is the `p` differences of
   those two tuples of pullbacks. Subtraction of global sections is a ring operation and needs
   nothing new; each member is a section of `P` and of nothing smaller.
3. **The object.** `ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` of `P` at that family. Its
   immersion into `P` is a monomorphism, which is where uniqueness comes from.
4. **The square commutes.** `ComplexAnalytic.AnalyticSpace.hom_ext_ofCutOut` cancels the immersion
   of `S`, `ComplexAnalytic.AnalyticSpace.hom_ext_restrict_complexAffineSpace` reduces the
   remaining equation of morphisms into `ℂ^p|U` to the `p` coordinate pullbacks, and each of those
   is the vanishing of one member of the cutting family — which is free, from
   `ComplexAnalytic.AnalyticSpace.pullbackΓ_zeroLocusSubspaceι_eq_zero` and the fact that pulling
   a section back is a ring homomorphism. **This is the direction that needs the equality of two
   morphisms to be detected by coordinates**, and it is the whole of the new content.
5. **The lift.** A cone is a pair into `X` and `Y` whose composites to `S` agree.
   `ComplexAnalytic.AnalyticSpace.prodCutOutLift` puts it in `P`, and the cone's own commutation —
   pushed along `ComplexAnalytic.AnalyticSpace.toAffineOfCutOut` — is exactly the vanishing of the
   `p` differences, so `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift` factors it through the
   zero locus. **No `ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` is used here**: the
   cone's equation is transported forward and not detected.
6. **Uniqueness.** Two cancellations: the immersion into `P` is a monomorphism, and
   `ComplexAnalytic.AnalyticSpace.hom_ext_prodCutOut` is uniqueness in `P`.

**Nothing here is analysis and nothing here computes a stalk.** Every step is a cancellation, a
ring operation on global sections, or a lemma of `Oka/AnalyticSpace/CutOutProduct.lean` and
`Oka/AnalyticSpace/ZeroLocus.lean` applied to the output of the one before it.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift`: **the mapping property of the zero locus
  of global sections**, at the analytic level.
- `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceHom`: **the morphism between zero loci a
  morphism of the ambient spaces induces**, when the family upstairs is the pullback of the one
  downstairs.
- `ComplexAnalytic.AnalyticSpace.toAffineOfCutOut`: a local model read in `ℂ^p`.
- `ComplexAnalytic.AnalyticSpace.eqCutFamily`: **the `p` differences that cut the fibre product
  out of the product.**
- `ComplexAnalytic.AnalyticSpace.fibreProdCutOut`: **the fibre product object.**
- `ComplexAnalytic.AnalyticSpace.fibreProdCutOutι`: its immersion into the product.
- `ComplexAnalytic.AnalyticSpace.fibreProdCutOutFst` and
  `ComplexAnalytic.AnalyticSpace.fibreProdCutOutSnd`: the two projections.
- `ComplexAnalytic.AnalyticSpace.fibreProdCutOutLift`: the morphism a cone induces.
- `ComplexAnalytic.AnalyticSpace.fibreProdCutOutIsoPullback`: the identification of
  `ComplexAnalytic.AnalyticSpace.fibreProdCutOut` with `CategoryTheory.Limits.pullback a b`.

## Main results

- `ComplexAnalytic.AnalyticSpace.hom_ext_restrict_complexAffineSpace`: **a morphism into an open
  subspace of `ℂ^p` is determined by the coordinate pullbacks of its composite with the
  inclusion.**
- `ComplexAnalytic.AnalyticSpace.hom_ext_zeroLocusSubspace`: a morphism into the zero locus is
  determined by its composite with the immersion.
- `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceHom_comp` and
  `ComplexAnalytic.AnalyticSpace.isFinite_zeroLocusSubspaceHom`: **that morphism is over the one
  it is induced by, and it is finite whenever that one is.** The second is the first consumer of
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy_of_comp_eq`
  (`Oka/AnalyticSpace/Finite.lean`).
- `ComplexAnalytic.AnalyticSpace.fibreProdCutOut_condition`: **the square commutes.**
- `ComplexAnalytic.AnalyticSpace.fibreProdCutOutLift_fst`,
  `ComplexAnalytic.AnalyticSpace.fibreProdCutOutLift_snd` and
  `ComplexAnalytic.AnalyticSpace.hom_ext_fibreProdCutOut`: the two triangles and uniqueness.
- `ComplexAnalytic.AnalyticSpace.isLimitPullbackConeFibreProdCutOut` and
  `ComplexAnalytic.AnalyticSpace.isPullback_fibreProdCutOut`: **the square is a pullback square.**
- `ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut`: hence
  `CategoryTheory.Limits.HasPullback a b`, as an instance.

## What is not here

* **`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace`.**
  `#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` **fails** at the commit
  that adds this file — elaborated in a two-line `import Oka` probe with the category positional,
  so that it is fixed by the statement and not by a named argument, which is the false alarm taxis
  #1821 records — and it will keep failing until the local fibre products below are glued. A
  general analytic space is only *locally* a local model, and gluing is the next rung; this
  repository has the machinery for it in `Oka/CategoryTheory/GlueData.lean`,
  `Oka/AnalyticSpace/Glue.lean` and `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`, and
  nothing below uses any of it. **A reader who takes this file for the general fibre product has
  been misled, and this paragraph is what prevents that.**

  **The gluing happened and the prediction held exactly.**
  `Oka/AnalyticSpace/PullbackReduction.lean` made
  `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` a theorem on 2026-09-08,
  and `ComplexAnalytic.AnalyticSpace.hasPullback_of_isCutOutModel` — its base case — is
  `ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` below with three presentations substituted
  in, so this file is the bottom rung of that ladder and not a detour from it. **Every sentence
  above stands**: the `#synth` is pinned to the commit that adds this file, *below* is this file,
  and a reader who takes this file for the general fibre product is still misled — the general one
  is four declarations further on.
* **Nothing about the fibre product on points.** The carrier of
  `ComplexAnalytic.AnalyticSpace.fibreProdCutOut` is the zero locus of the differences inside the
  carrier of the product, and no statement below identifies it with a set of pairs agreeing over
  `S`, in the way `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` does for its own base change with
  `Function.Pullback`.
* **`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for any class.** That quantifies over
  every cospan with a leg in the class, including cospans of spaces that are not local models, and
  nothing below carries a class across the square built here.

  **The sentence above is unchanged by the push that adds
  `ComplexAnalytic.AnalyticSpace.isFinite_zeroLocusSubspaceHom` below, and this paragraph is why it
  did not have to change.** That theorem *does* carry a class across a square: it carries
  `ComplexAnalytic.AnalyticSpace.IsFinite` across
  `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceHom_comp`, the square of a zero locus and the zero
  locus of its pulled-back family. But that is not *the square built here* — the square built here
  is the fibre-product one, and nothing below carries a class across **that**, which is what the
  sentence says and said before. The square it does carry one across is a commuting square and not
  a limit: nothing below identifies its source with a fibre product. **So nothing in this bullet is
  retired by that push**, and the class quantifier is untouched either way, one class across one
  shape of commuting square not being `IsStableUnderBaseChange` for any class.
* **Independence of the presentations.** `ComplexAnalytic.AnalyticSpace.fibreProdCutOut` is indexed
  by the three cutting families and the two morphisms, exactly as
  `ComplexAnalytic.AnalyticSpace.prodCutOut` is indexed by two families; two presentations of the
  same three spaces give two objects, canonically isomorphic through
  `ComplexAnalytic.AnalyticSpace.fibreProdCutOutIsoPullback` at each. Nothing below states that
  isomorphism.
* **The diagonal, and hence nothing about separatedness.** `A ⟶ A ×_S A` is an instance of the
  square below at `a = b`, and no declaration below names it or reads anything off it. That is
  what taxis #1772's monomorphism argument wants, and it wants it for arbitrary covers rather than
  for local models.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

/-! ### Two mapping properties, in the shape this file consumes them -/

section MappingProperty

variable {Z : AnalyticSpace.{u}} {p : ℕ} {U : (AnalyticSpace.complexAffineSpace.{u} p).Opens}

/-- **A morphism into an open subspace of `ℂ^p` is determined by the coordinate pullbacks of its
composite with the inclusion.**

`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` is the statement at `ℂ^p` itself; the
inclusion of an open subspace is a monomorphism
(`ComplexAnalytic.AnalyticSpace.mono_ofRestrict`), so it cancels, and that is the whole proof.

The hypothesis is stated in the `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` spelling rather than
in the `AlgebraicGeometry.LocallyRingedSpace.Γ.map` one it is definitionally equal to, for the
reason that abbreviation's own docstring gives: a goal carrying a raw `Γ.map … |>.hom` term is not
type-correct under the `instances` transparency level, and it is the rewrite *after* the one that
introduced it which fails. -/
theorem hom_ext_restrict_complexAffineSpace
    (φ ψ : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} p).restrict U)
    (hco : ∀ j : ULift.{u} (Fin p),
      (φ ≫ (AnalyticSpace.complexAffineSpace.{u} p).ofRestrict U).pullbackΓ (coord j) =
        (ψ ≫ (AnalyticSpace.complexAffineSpace.{u} p).ofRestrict U).pullbackΓ (coord j)) :
    φ = ψ :=
  (cancel_mono ((AnalyticSpace.complexAffineSpace.{u} p).ofRestrict U)).1
    (hom_ext_complexAffineSpace _ _ hco)

variable {X : AnalyticSpace.{u}} {s : Fin p → X.presheaf.obj (op ⊤)}

/-- **A morphism of analytic spaces killing finitely many global sections of its target factors
through their zero locus.**

`ComplexAnalytic.IsCutOutBy.lift` supplies the underlying morphism of locally ringed spaces and
`ComplexAnalytic.IsCutOutBy.isCLinearHom_lift` supplies its `ℂ`-linearity. **No transport of
algebra structures happens**: the structure
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` carries is by definition the ambient one pulled
back along the immersion — that is
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspace_algebraMap` — and it is the structure the second
of those two lemmas concludes about, on the nose.

This is the mapping property `Oka/AnalyticSpace/ZeroLocus.lean`'s `## What is not here` names and
does not compose; see this file's header for why that file could not have stated it. -/
def zeroLocusSubspaceLift (φ : Z ⟶ X) (hφ : ∀ j, φ.pullbackΓ (s j) = 0) :
    Z ⟶ X.zeroLocusSubspace s :=
  ⟨(X.isCutOutBy_zeroLocusSubspaceι s).lift φ.toLRSHom hφ,
    (X.isCutOutBy_zeroLocusSubspaceι s).isCLinearHom_lift _ _ φ.isCLinear⟩

/-- **The factorisation followed by the immersion is the original morphism.**

`ComplexAnalytic.IsCutOutBy.lift_comp` pushed up along
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`, which is faithful. This equation and
not `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift` itself is what every proof below
consumes. -/
@[simp]
lemma zeroLocusSubspaceLift_comp (φ : Z ⟶ X) (hφ : ∀ j, φ.pullbackΓ (s j) = 0) :
    zeroLocusSubspaceLift φ hφ ≫ X.zeroLocusSubspaceι s = φ :=
  forgetToLocallyRingedSpace.map_injective
    ((X.isCutOutBy_zeroLocusSubspaceι s).lift_comp φ.toLRSHom hφ)

/-- **A morphism into the zero locus is determined by its composite with the immersion**, which is
`ComplexAnalytic.AnalyticSpace.mono_zeroLocusSubspaceι` in the form a cancellation argument
uses. -/
theorem hom_ext_zeroLocusSubspace (ψ₁ ψ₂ : Z ⟶ X.zeroLocusSubspace s)
    (h : ψ₁ ≫ X.zeroLocusSubspaceι s = ψ₂ ≫ X.zeroLocusSubspaceι s) : ψ₁ = ψ₂ :=
  (cancel_mono (X.zeroLocusSubspaceι s)).1 h

end MappingProperty

/-! ### The zero locus of a pulled-back family, over the zero locus of the family -/

section ZeroLocusHom

variable {E B : AnalyticSpace.{u}} {k : ℕ}

/-- **The zero locus of a pulled-back family, over the zero locus of the family.**

For `φ : E ⟶ B` and global sections `s` of `B`, the zero locus of `fun j ↦ φ.pullbackΓ (s j)` in
`E` maps to the zero locus of `s` in `B`, over `φ`. It is
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift` applied to the immersion followed by `φ`,
whose pullbacks of the `s j` vanish by
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ_comp` and
`ComplexAnalytic.AnalyticSpace.pullbackΓ_zeroLocusSubspaceι_eq_zero`.

**Nothing here identifies this with a fibre product, and nothing below needs the
identification.** What the finiteness statement consumes is the square, and no declaration of this
repository says that the zero locus of a pulled-back family is a `CategoryTheory.Limits.pullback`
— the only `CategoryTheory.IsPullback` below is
`ComplexAnalytic.AnalyticSpace.isPullback_fibreProdCutOut`, about the other square. -/
def zeroLocusSubspaceHom (φ : E ⟶ B) (s : Fin k → B.presheaf.obj (op ⊤)) :
    E.zeroLocusSubspace (fun j ↦ φ.pullbackΓ (s j)) ⟶ B.zeroLocusSubspace s :=
  zeroLocusSubspaceLift (E.zeroLocusSubspaceι (fun j ↦ φ.pullbackΓ (s j)) ≫ φ) fun j ↦ by
    rw [Hom.pullbackΓ_comp]
    exact E.pullbackΓ_zeroLocusSubspaceι_eq_zero (fun j ↦ φ.pullbackΓ (s j)) j

/-- **The square commutes**: the comparison followed by the immersion of the zero locus of `s` is
the immersion of the zero locus of the pulled-back family followed by `φ`. This is
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift_comp` at the datum above, and it is the whole
of what the theorem below reads. -/
@[simp]
lemma zeroLocusSubspaceHom_comp (φ : E ⟶ B) (s : Fin k → B.presheaf.obj (op ⊤)) :
    zeroLocusSubspaceHom φ s ≫ B.zeroLocusSubspaceι s =
      E.zeroLocusSubspaceι (fun j ↦ φ.pullbackΓ (s j)) ≫ φ :=
  zeroLocusSubspaceLift_comp _ _

/-- **Finiteness is carried across a zero locus.** If `φ` is finite then so is the morphism it
induces between the zero locus of a pulled-back family and the zero locus of the family.

`ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy_of_comp_eq`
(`Oka/AnalyticSpace/Finite.lean`) at the square above and the two cut-out data
`ComplexAnalytic.AnalyticSpace.isCutOutBy_zeroLocusSubspaceι` supplies on each side. **Only the
`IsFinite` half is asked**: the base-change statements of
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` are stated under `[IsFiniteEtale q]` — including
`ComplexAnalytic.AnalyticSpace.isClosedMap_baseChangeSndBase` and
`ComplexAnalytic.AnalyticSpace.finite_fiber_baseChangeSndBase`, which spend only its `IsFinite`
field — and `Oka/AnalyticSpace/PullbackOpen.lean`'s
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` is along an open subspace, so neither reaches
a closed one.

**No limit is constructed and none is needed.** The statement is about the square, so it does not
wait on an identification of the source with a fibre product of `φ` and the immersion below it —
an identification no declaration of this repository states. -/
theorem isFinite_zeroLocusSubspaceHom (φ : E ⟶ B) [IsFinite φ]
    (s : Fin k → B.presheaf.obj (op ⊤)) : IsFinite (zeroLocusSubspaceHom φ s) :=
  isFinite_of_isCutOutBy_of_comp_eq (B.isCutOutBy_zeroLocusSubspaceι s)
    (E.isCutOutBy_zeroLocusSubspaceι _) (zeroLocusSubspaceHom_comp φ s)

end ZeroLocusHom

/-! ### The fibre product of two local models over a third -/

section FibreProduct

variable {n m p k l q : ℕ}
  {V : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
  {W : (AnalyticSpace.complexAffineSpace.{u} m).Opens}
  {U : (AnalyticSpace.complexAffineSpace.{u} p).Opens}
  {MX MY MS : LocallyRingedSpace.{u}}
  {iX : MX ⟶ (_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding}
  {iY : MY ⟶ (_root_.complexAffineSpace.{u} m).restrict W.isOpenEmbedding}
  {iS : MS ⟶ (_root_.complexAffineSpace.{u} p).restrict U.isOpenEmbedding}
  {f : Fin k → ((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)}
  {g : Fin l → ((_root_.complexAffineSpace.{u} m).restrict W.isOpenEmbedding).presheaf.obj (op ⊤)}
  {h : Fin q → ((_root_.complexAffineSpace.{u} p).restrict U.isOpenEmbedding).presheaf.obj (op ⊤)}

variable (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g) (hS : IsCutOutBy iS h)

/-- **The base local model read in the whole of `ℂ^p`**: its closed immersion into `ℂ^p|U`
followed by the inclusion of that open subspace.

Composing with the inclusion is a design choice and it is the same one
`ComplexAnalytic.AnalyticSpace.exists_chartLift` makes: it puts the two composites of the square
into `ℂ^p` rather than into `ℂ^p|U`, so that their coordinate pullbacks are pullbacks of
`ComplexAnalytic.coord` and `ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` is
available to compare them. Nothing is lost, because
`ComplexAnalytic.AnalyticSpace.hom_ext_restrict_complexAffineSpace` cancels the inclusion back
off. -/
def toAffineOfCutOut : AnalyticSpace.ofCutOut hS ⟶ AnalyticSpace.complexAffineSpace.{u} p :=
  ofCutOutHom hS ≫ (AnalyticSpace.complexAffineSpace.{u} p).ofRestrict U

variable (a : AnalyticSpace.ofCutOut hX ⟶ AnalyticSpace.ofCutOut hS)
  (b : AnalyticSpace.ofCutOut hY ⟶ AnalyticSpace.ofCutOut hS)

/-- **The `p` sections of the product that cut the fibre product out of it**: the differences of
the coordinate pullbacks of the two composites `X × Y ⟶ ℂ^p`.

These are global sections of `ComplexAnalytic.AnalyticSpace.prodCutOut` and **not** pullbacks of
sections of its ambient `ℂ^(n+m)|affineProdOpens V W`, which is the whole difference between this
file and `Oka/AnalyticSpace/CutOutProduct.lean` and the reason the object below is a
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` rather than a
`ComplexAnalytic.AnalyticSpace.ofCutOut`. See this file's header. -/
def eqCutFamily : Fin p → (prodCutOut.{u} f g).presheaf.obj (op ⊤) :=
  fun j ↦ (prodCutOutFst.{u} hX g ≫ a ≫ toAffineOfCutOut hS).pullbackΓ (coord (ULift.up j)) -
    (prodCutOutSnd.{u} f hY ≫ b ≫ toAffineOfCutOut hS).pullbackΓ (coord (ULift.up j))

/-- **The fibre product of two local models over a third**: the zero locus, inside their binary
product, of the `p` differences of the two composites to `ℂ^p`.

Nothing below presents this as a local model, and nothing below claims it is one. What it is, is
an object of `ComplexAnalytic.AnalyticSpace`, which is what
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` produces from any analytic space and any finite
family of its global sections. -/
def fibreProdCutOut : AnalyticSpace.{u} :=
  (prodCutOut.{u} f g).zeroLocusSubspace (eqCutFamily hX hY hS a b)

/-- **The closed immersion of the fibre product into the product.** -/
def fibreProdCutOutι : fibreProdCutOut hX hY hS a b ⟶ prodCutOut.{u} f g :=
  (prodCutOut.{u} f g).zeroLocusSubspaceι _

/-- **The first projection of the fibre product**, the immersion into the product followed by the
product's first projection. -/
def fibreProdCutOutFst : fibreProdCutOut hX hY hS a b ⟶ AnalyticSpace.ofCutOut hX :=
  fibreProdCutOutι hX hY hS a b ≫ prodCutOutFst.{u} hX g

/-- **The second projection of the fibre product.** -/
def fibreProdCutOutSnd : fibreProdCutOut hX hY hS a b ⟶ AnalyticSpace.ofCutOut hY :=
  fibreProdCutOutι hX hY hS a b ≫ prodCutOutSnd.{u} f hY

/-- The first projection, factored through the immersion into the product. `rfl`, stated so that
the rewrites below fire on it: a `def` is opaque to `rw` and its auto-generated equation lemma is
a declaration this file would then owe a guard on. -/
lemma fibreProdCutOutFst_eq :
    fibreProdCutOutFst hX hY hS a b = fibreProdCutOutι hX hY hS a b ≫ prodCutOutFst.{u} hX g := rfl

/-- The second projection, factored through the immersion into the product. -/
lemma fibreProdCutOutSnd_eq :
    fibreProdCutOutSnd hX hY hS a b = fibreProdCutOutι hX hY hS a b ≫ prodCutOutSnd.{u} f hY := rfl

/-- **The two composites to `ℂ^p` agree after the immersion of the fibre product**, coordinate by
coordinate.

The `j`-th difference is a member of the cutting family, so it pulls back to zero along the
immersion — `ComplexAnalytic.AnalyticSpace.pullbackΓ_zeroLocusSubspaceι_eq_zero`, which is free
— and pulling a section back is a ring homomorphism, so that vanishing *is* the equality of the
two pullbacks. This is the only place where `map_sub` is used, and using it as a term rather than
a rewrite is what keeps the goal inside the
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` spelling. -/
theorem pullbackΓ_eqCutFamily_fibreProdCutOutι (j : Fin p) :
    (fibreProdCutOutι hX hY hS a b).pullbackΓ
        ((prodCutOutFst.{u} hX g ≫ a ≫ toAffineOfCutOut hS).pullbackΓ (coord (ULift.up j))) =
      (fibreProdCutOutι hX hY hS a b).pullbackΓ
        ((prodCutOutSnd.{u} f hY ≫ b ≫ toAffineOfCutOut hS).pullbackΓ (coord (ULift.up j))) :=
  sub_eq_zero.1
    ((map_sub (LocallyRingedSpace.Γ.map
        (fibreProdCutOutι hX hY hS a b).toLRSHom.op).hom _ _).symm.trans
      ((prodCutOut.{u} f g).pullbackΓ_zeroLocusSubspaceι_eq_zero (eqCutFamily hX hY hS a b) j))

set_option backward.isDefEq.respectTransparency false in
/-- **The square commutes**: the two projections of the fibre product followed by the two legs of
the cospan agree.

Two cancellations and then coordinates. `ComplexAnalytic.AnalyticSpace.hom_ext_ofCutOut` cancels
the immersion of the base local model, leaving an equation of morphisms into `ℂ^p|U`;
`ComplexAnalytic.AnalyticSpace.hom_ext_restrict_complexAffineSpace` reduces that to the `p`
coordinate pullbacks; and each of those is
`ComplexAnalytic.AnalyticSpace.pullbackΓ_eqCutFamily_fibreProdCutOutι`. **This is the step that
needs equality of morphisms to be detected by coordinates**, and it is the only one that does. -/
theorem fibreProdCutOut_condition :
    fibreProdCutOutFst hX hY hS a b ≫ a = fibreProdCutOutSnd hX hY hS a b ≫ b := by
  refine hom_ext_ofCutOut hS _ _ (hom_ext_restrict_complexAffineSpace _ _ fun j ↦ ?_)
  have key := pullbackΓ_eqCutFamily_fibreProdCutOutι hX hY hS a b j.down
  rw [← Hom.pullbackΓ_comp, ← Hom.pullbackΓ_comp] at key
  rw [fibreProdCutOutFst_eq, fibreProdCutOutSnd_eq]
  simp only [Category.assoc] at key ⊢
  exact key

set_option backward.isDefEq.respectTransparency false in
/-- **A cone over the cospan kills the `p` differences.**

The cone's pair into the product is `ComplexAnalytic.AnalyticSpace.prodCutOutLift`, and
`ComplexAnalytic.AnalyticSpace.prodCutOutLift_fst` and
`ComplexAnalytic.AnalyticSpace.prodCutOutLift_snd` identify its composites with the two
projections. So each difference pulls back to the difference of the two sides of the cone's own
commutation, read in `ℂ^p`, which is zero. **Nothing detects an equality here** — the cone's
equation is transported forward, which is why no
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` appears in this direction. -/
theorem pullbackΓ_prodCutOutLift_eqCutFamily {Z : AnalyticSpace.{u}}
    (u : Z ⟶ AnalyticSpace.ofCutOut hX) (v : Z ⟶ AnalyticSpace.ofCutOut hY)
    (hc : u ≫ a = v ≫ b) (j : Fin p) :
    (prodCutOutLift hX hY u v).pullbackΓ (eqCutFamily hX hY hS a b j) = 0 := by
  have h₁ : prodCutOutLift hX hY u v ≫ prodCutOutFst.{u} hX g ≫ a ≫ toAffineOfCutOut hS
      = u ≫ a ≫ toAffineOfCutOut hS := by
    rw [← Category.assoc, prodCutOutLift_fst]
  have h₂ : prodCutOutLift hX hY u v ≫ prodCutOutSnd.{u} f hY ≫ b ≫ toAffineOfCutOut hS
      = v ≫ b ≫ toAffineOfCutOut hS := by
    rw [← Category.assoc, prodCutOutLift_snd]
  have hcc : u ≫ a ≫ toAffineOfCutOut hS = v ≫ b ≫ toAffineOfCutOut hS := by
    rw [← Category.assoc, hc, Category.assoc]
  have hms : (prodCutOutLift hX hY u v).pullbackΓ (eqCutFamily hX hY hS a b j) =
      (prodCutOutLift hX hY u v).pullbackΓ
          ((prodCutOutFst.{u} hX g ≫ a ≫ toAffineOfCutOut hS).pullbackΓ (coord (ULift.up j))) -
        (prodCutOutLift hX hY u v).pullbackΓ
          ((prodCutOutSnd.{u} f hY ≫ b ≫ toAffineOfCutOut hS).pullbackΓ (coord (ULift.up j))) :=
    map_sub _ _ _
  rw [hms, sub_eq_zero, ← Hom.pullbackΓ_comp, ← Hom.pullbackΓ_comp, h₁, h₂, hcc]

/-- **The morphism into the fibre product that a cone induces.**

`ComplexAnalytic.AnalyticSpace.prodCutOutLift` into the product, factored through the zero locus
by `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift`. -/
def fibreProdCutOutLift {Z : AnalyticSpace.{u}} (u : Z ⟶ AnalyticSpace.ofCutOut hX)
    (v : Z ⟶ AnalyticSpace.ofCutOut hY) (hc : u ≫ a = v ≫ b) :
    Z ⟶ fibreProdCutOut hX hY hS a b :=
  zeroLocusSubspaceLift (prodCutOutLift hX hY u v)
    (pullbackΓ_prodCutOutLift_eqCutFamily hX hY hS a b u v hc)

/-- **The induced morphism followed by the immersion is the pair taken in the product**, which is
how the two triangles reach `ComplexAnalytic.AnalyticSpace.prodCutOutLift_fst` and
`ComplexAnalytic.AnalyticSpace.prodCutOutLift_snd`. -/
theorem fibreProdCutOutLift_ι {Z : AnalyticSpace.{u}} (u : Z ⟶ AnalyticSpace.ofCutOut hX)
    (v : Z ⟶ AnalyticSpace.ofCutOut hY) (hc : u ≫ a = v ≫ b) :
    fibreProdCutOutLift hX hY hS a b u v hc ≫ fibreProdCutOutι hX hY hS a b =
      prodCutOutLift hX hY u v :=
  zeroLocusSubspaceLift_comp _ _

/-- **The first triangle.** -/
theorem fibreProdCutOutLift_fst {Z : AnalyticSpace.{u}} (u : Z ⟶ AnalyticSpace.ofCutOut hX)
    (v : Z ⟶ AnalyticSpace.ofCutOut hY) (hc : u ≫ a = v ≫ b) :
    fibreProdCutOutLift hX hY hS a b u v hc ≫ fibreProdCutOutFst hX hY hS a b = u := by
  rw [fibreProdCutOutFst_eq, ← Category.assoc, fibreProdCutOutLift_ι, prodCutOutLift_fst]

/-- **The second triangle.** -/
theorem fibreProdCutOutLift_snd {Z : AnalyticSpace.{u}} (u : Z ⟶ AnalyticSpace.ofCutOut hX)
    (v : Z ⟶ AnalyticSpace.ofCutOut hY) (hc : u ≫ a = v ≫ b) :
    fibreProdCutOutLift hX hY hS a b u v hc ≫ fibreProdCutOutSnd hX hY hS a b = v := by
  rw [fibreProdCutOutSnd_eq, ← Category.assoc, fibreProdCutOutLift_ι, prodCutOutLift_snd]

/-- **A morphism into the fibre product is determined by its composite with the immersion**, which
is `ComplexAnalytic.AnalyticSpace.hom_ext_zeroLocusSubspace` at this object, restated so that the
goal is phrased in `ComplexAnalytic.AnalyticSpace.fibreProdCutOutι` and the rewrites of
`ComplexAnalytic.AnalyticSpace.hom_ext_fibreProdCutOut` fire on it. -/
theorem hom_ext_fibreProdCutOutι {Z : AnalyticSpace.{u}}
    (φ ψ : Z ⟶ fibreProdCutOut hX hY hS a b)
    (hh : φ ≫ fibreProdCutOutι hX hY hS a b = ψ ≫ fibreProdCutOutι hX hY hS a b) : φ = ψ :=
  hom_ext_zeroLocusSubspace _ _ hh

/-- **A morphism into the fibre product is determined by its two projections.**

Two cancellations and no computation: the immersion into the product is a monomorphism, and
`ComplexAnalytic.AnalyticSpace.hom_ext_prodCutOut` is uniqueness in the product. **The cone's
commutation is not used**, which is the sense in which uniqueness here is uniqueness in the
product and nothing more. -/
theorem hom_ext_fibreProdCutOut {Z : AnalyticSpace.{u}}
    (φ ψ : Z ⟶ fibreProdCutOut hX hY hS a b)
    (h₁ : φ ≫ fibreProdCutOutFst hX hY hS a b = ψ ≫ fibreProdCutOutFst hX hY hS a b)
    (h₂ : φ ≫ fibreProdCutOutSnd hX hY hS a b = ψ ≫ fibreProdCutOutSnd hX hY hS a b) : φ = ψ := by
  refine hom_ext_fibreProdCutOutι hX hY hS a b _ _ (hom_ext_prodCutOut hX hY _ _ ?_ ?_)
  · rw [Category.assoc, Category.assoc, ← fibreProdCutOutFst_eq, h₁]
  · rw [Category.assoc, Category.assoc, ← fibreProdCutOutSnd_eq, h₂]

/-- **The fibre product with its two projections, as a cone over the cospan.** -/
def pullbackConeFibreProdCutOut : PullbackCone a b :=
  PullbackCone.mk (fibreProdCutOutFst hX hY hS a b) (fibreProdCutOutSnd hX hY hS a b)
    (fibreProdCutOut_condition hX hY hS a b)

/-- **That cone is a limit**, so the zero locus of the `p` differences is the fibre product of the
two local models over the third.

The lift is `ComplexAnalytic.AnalyticSpace.fibreProdCutOutLift` at the cone's two legs and its own
commutation, the two triangles are
`ComplexAnalytic.AnalyticSpace.fibreProdCutOutLift_fst` and
`ComplexAnalytic.AnalyticSpace.fibreProdCutOutLift_snd`, and uniqueness is
`ComplexAnalytic.AnalyticSpace.hom_ext_fibreProdCutOut`. -/
def isLimitPullbackConeFibreProdCutOut : IsLimit (pullbackConeFibreProdCutOut hX hY hS a b) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ fibreProdCutOutLift hX hY hS a b s.fst s.snd s.condition)
    (fun s ↦ fibreProdCutOutLift_fst hX hY hS a b s.fst s.snd s.condition)
    (fun s ↦ fibreProdCutOutLift_snd hX hY hS a b s.fst s.snd s.condition)
    fun _ _ h₁ h₂ ↦ hom_ext_fibreProdCutOut hX hY hS a b _ _
      (by rw [h₁, fibreProdCutOutLift_fst]) (by rw [h₂, fibreProdCutOutLift_snd])

/-- **The square is a pullback square**, in the `CategoryTheory.IsPullback` spelling
`Oka/AnalyticSpace/PullbackOpen.lean` and `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` state
their own squares in. -/
theorem isPullback_fibreProdCutOut :
    IsPullback (fibreProdCutOutFst hX hY hS a b) (fibreProdCutOutSnd hX hY hS a b) a b :=
  IsPullback.of_isLimit (isLimitPullbackConeFibreProdCutOut hX hY hS a b)

/-- **A cospan of local models presented by cut-out data has a pullback.**

`CategoryTheory.Limits.HasPullback` is `Prop`-valued, so this instance loses the identification of
the limit with the zero locus;
`ComplexAnalytic.AnalyticSpace.isLimitPullbackConeFibreProdCutOut` is what keeps it, and
`ComplexAnalytic.AnalyticSpace.fibreProdCutOutIsoPullback` is that identification stated against
the notation. -/
instance hasPullback_ofCutOut : HasPullback a b :=
  ⟨⟨_, isLimitPullbackConeFibreProdCutOut hX hY hS a b⟩⟩

/-- **The zero locus of the `p` differences is `CategoryTheory.Limits.pullback a b`**, as an
isomorphism against the notation.

Two limits over the same cospan, so
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`. **The statement does not elaborate unless
`ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` is found by instance search**, since
`CategoryTheory.Limits.pullback` is a `CategoryTheory.Limits.limit` that needs it; so this
declaration, and the guard on it, test that the instance is found and not merely that it exists.
That is the device `ComplexAnalytic.AnalyticSpace.prodCutOutIsoProd` uses for the binary
product. -/
def fibreProdCutOutIsoPullback : fibreProdCutOut hX hY hS a b ≅ Limits.pullback a b :=
  (isLimitPullbackConeFibreProdCutOut hX hY hS a b).conePointUniqueUpToIso (limit.isLimit _)

end FibreProduct

end ComplexAnalytic.AnalyticSpace
