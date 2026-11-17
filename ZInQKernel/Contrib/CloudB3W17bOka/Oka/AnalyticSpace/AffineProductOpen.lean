/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.AffineProduct
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.OpenSubspace

/-!
# The product of two open subspaces of complex affine spaces

`Oka/AnalyticSpace/AffineProduct.lean` makes `ℂ^(n+m)` the binary product of `ℂ^n` and `ℂ^m`.
That is the product of two *affine spaces*, and it is not the object a product of two local
models is built inside: a local model of this development is cut out inside an **open subset** of
some `ℂ^n`. `ComplexAnalytic.AnalyticSpace.zeroLocus` in `Oka/AnalyticSpace/LocalModel.lean` takes
an open `V` of `complexAffineSpace n` and cuts out inside
`(complexAffineSpace n).restrict V.isOpenEmbedding`, and that locally ringed space is the one
underlying `ComplexAnalytic.AnalyticSpace.restrict` at `V` — the two are the same term, which
`ComplexAnalytic.AnalyticSpace.restrict_toLocallyRingedSpace` says and which was checked with an
`rfl` in a scratch file rather than assumed. This file supplies that object: for
`V : Opens ℂ^n` and `W : Opens ℂ^m`, the open subspace of `ℂ^(n+m)` at
`ComplexAnalytic.AnalyticSpace.affineProdOpens V W` — the meet of the two preimages — **is** the
binary product of `ℂ^n|V` and `ℂ^m|W`.

Every construction here is assembled from declarations this file imports. The object is
`ComplexAnalytic.AnalyticSpace.restrict` at an `Opens.map` of an existing projection; the two
legs and the pair are `ComplexAnalytic.AnalyticSpace.liftRestrict`; the triangles are
`ComplexAnalytic.AnalyticSpace.liftRestrict_fac` and the triangles of
`Oka/AnalyticSpace/AffineProduct.lean`; and uniqueness is
`ComplexAnalytic.AnalyticSpace.mono_ofRestrict` against
`ComplexAnalytic.AnalyticSpace.hom_ext_affineProd`. It is an assembly, in the sense
`Oka/AnalyticSpace/PullbackOpen.lean` is one.

## The range condition, which is the only step with content

`ComplexAnalytic.AnalyticSpace.liftRestrict` asks that the range of the base map of the morphism
being lifted lie in the open. For the pair that is the statement that
`ComplexAnalytic.AnalyticSpace.affineProdLift` of two morphisms landing in `V` and in `W` lands in
the meet of the two preimages, and **it is discharged from the triangles rather than from a
formula on points**: `ComplexAnalytic.AnalyticSpace.affineProdLift_fst` says the pair followed by
the first projection is the first morphism, so applying the base map of the first projection to a
point of the pair's image gives a point of the first morphism's image, which lies in `V` by
assumption. The base maps of the two projections computed in this file are not used for it.

`congrArg` produces that equation as a statement about the base map of a *composite*, and `rw`
cannot see through the composite; the `have`s in
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift` therefore carry a type ascription that states
it in the applied form, which is definitionally the same and syntactically what the goal has.

## The base maps

`Oka/AnalyticSpace/AffineProduct.lean` defines its projections by their coordinate pullbacks, and
at `bbbc91f` its `## What is not here` says of that file that it does not compute their base maps
and that no statement in it needs one. This file does compute them, in one rewrite each, because
a consumer that cuts something out of the product will describe the cutting on points:
`ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback` in
`Oka/AnalyticSpace/HomToComplex.lean` turns a coordinate of the image point into the value of a
pulled-back coordinate, `ComplexAnalytic.AnalyticSpace.coordPullback_affineProdFst` says which
coordinate that is, and `ComplexAnalytic.AnalyticSpace.eval_coord` reads it off. The `funext`
form of each — the base map as a function rather than at an index — is one application of
`funext` to the statement given here and is not stated, no declaration in this file consuming it.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.affineProdOpens`: the open of `ℂ^(n+m)` at which a pair of
  opens, one of `ℂ^n` and one of `ℂ^m`, cuts out their product.
- `ComplexAnalytic.AnalyticSpace.affineProdOpensFst` and
  `ComplexAnalytic.AnalyticSpace.affineProdOpensSnd`: the two legs.
- `ComplexAnalytic.AnalyticSpace.affineProdOpensLift`: the pair.
- `ComplexAnalytic.AnalyticSpace.affineProdOpensIsoProd`: the identification of
  `ℂ^(n+m)|affineProdOpens V W` with the categorical product `ℂ^n|V ⨯ ℂ^m|W`.

## Main results

- `ComplexAnalytic.AnalyticSpace.base_affineProdFst` and
  `ComplexAnalytic.AnalyticSpace.base_affineProdSnd`: **the base maps of the two coordinate
  projections of `ℂ^(n+m)`**, at an index — the `j`-th coordinate of the image of `w` under the
  first projection is `w` at `Fin.castAdd`, and under the second is `w` at `Fin.natAdd`.
- `ComplexAnalytic.AnalyticSpace.base_affineProdLift`: **the base map of the pair**, which is
  `Fin.addCases` of the base maps of the two morphisms it was assembled from.
- `ComplexAnalytic.AnalyticSpace.mem_affineProdOpens_iff`: membership of
  `ComplexAnalytic.AnalyticSpace.affineProdOpens` is membership of the two images.
- `ComplexAnalytic.AnalyticSpace.affineProdOpensLift_fst`,
  `ComplexAnalytic.AnalyticSpace.affineProdOpensLift_snd` and
  `ComplexAnalytic.AnalyticSpace.hom_ext_affineProdOpens`: the two triangles and uniqueness.
- `ComplexAnalytic.AnalyticSpace.isLimitBinaryFanAffineProdOpens`: **`ℂ^(n+m)|affineProdOpens V W`
  with those two legs is the binary product of `ℂ^n|V` and `ℂ^m|W`**, and
  `ComplexAnalytic.AnalyticSpace.hasBinaryProduct_restrict_complexAffineSpace` is the instance.

## What is not here

* **`CategoryTheory.Limits.HasBinaryProducts ComplexAnalytic.AnalyticSpace`.** What lands here is
  the product at a pair of *open subspaces of affine spaces* and nothing wider. At `bbbc91f`,
  which is this file's base, **with this file added to the tree**, `#synth
  CategoryTheory.Limits.HasBinaryProducts ComplexAnalytic.AnalyticSpace` fails — elaborated rather
  than grepped, and that is the form of the probe worth recording, since
  `ComplexAnalytic.AnalyticSpace.hasBinaryProduct_restrict_complexAffineSpace` below could be
  mistaken for it. `#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` fails
  there too, `Oka/AnalyticSpace/PullbackOpen.lean` giving the pullback along one leg and not the
  class.
* **The product of two local models.** The product of a subspace cut out in `ℂ^n|V` and one cut
  out in `ℂ^m|W` is cut out inside the object built here, by the two families of functions pulled
  back along the two legs. Nothing below pulls a function back along either leg or takes a zero
  locus in the product.
* **Anything over a base.** Both statements here are absolute products. The fibre product over a
  common base is an equaliser inside such a product, and no construction below builds an
  equaliser or bears on `CategoryTheory.Limits.HasPullback`.
* **The topology of the identification.** `ComplexAnalytic.AnalyticSpace.affineProdOpensIsoProd`
  is an isomorphism of complex analytic spaces, which carries a homeomorphism of the underlying
  spaces with it; no statement below extracts that homeomorphism or describes it on points.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

/-! ### The base maps of the two projections and of the pair -/

variable (n m : ℕ)

/-- **The first projection `ℂ^(n+m) ⟶ ℂ^n` sends `w` to its first `n` coordinates.**

`ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback` computes a coordinate of an image
point as the value of a pulled-back coordinate,
`ComplexAnalytic.AnalyticSpace.coordPullback_affineProdFst` says that pullback is the
`Fin.castAdd`-th coordinate function of `ℂ^(n+m)`, and
`ComplexAnalytic.AnalyticSpace.eval_coord` says the value of a coordinate function at a point is
that coordinate of the point. -/
theorem base_affineProdFst (w : AnalyticSpace.complexAffineSpace.{u} (n + m))
    (j : ULift.{u} (Fin n)) :
    ((affineProdFst.{u} n m).toLRSHom.base w : ULift.{u} (Fin n) → ℂ) j =
      (w : ULift.{u} (Fin (n + m)) → ℂ) (ULift.up (Fin.castAdd m j.down)) := by
  rw [base_eq_eval_coordPullback, coordPullback_affineProdFst, eval_coord]

/-- **The second projection `ℂ^(n+m) ⟶ ℂ^m` sends `w` to its last `m` coordinates**, by the
argument `ComplexAnalytic.AnalyticSpace.base_affineProdFst` gives with
`ComplexAnalytic.AnalyticSpace.coordPullback_affineProdSnd` in place of
`ComplexAnalytic.AnalyticSpace.coordPullback_affineProdFst`. -/
theorem base_affineProdSnd (w : AnalyticSpace.complexAffineSpace.{u} (n + m))
    (j : ULift.{u} (Fin m)) :
    ((affineProdSnd.{u} n m).toLRSHom.base w : ULift.{u} (Fin m) → ℂ) j =
      (w : ULift.{u} (Fin (n + m)) → ℂ) (ULift.up (Fin.natAdd n j.down)) := by
  rw [base_eq_eval_coordPullback, coordPullback_affineProdSnd, eval_coord]

variable {n m}

/-- **The pair of two morphisms sends a point to the concatenation of the two images.**

`ComplexAnalytic.AnalyticSpace.coordPullback_affineProdLift` puts a `Fin.addCases` in the way, and
each branch is `ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback` read backwards at the
morphism that branch came from.

**The `obtain ⟨j⟩` before the induction is load-bearing.** `Fin.addCases` eliminates a
`Fin (n + m)`, and the index here is a `ULift` of one; destructing it first is what lets the
`induction` generalise, and without that step neither branch closes. -/
theorem base_affineProdLift {Z : AnalyticSpace.{u}}
    (f : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n)
    (g : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) (z : Z) (j : ULift.{u} (Fin (n + m))) :
    ((affineProdLift.{u} f g).toLRSHom.base z : ULift.{u} (Fin (n + m)) → ℂ) j =
      Fin.addCases (fun a ↦ (f.toLRSHom.base z : ULift.{u} (Fin n) → ℂ) (ULift.up a))
        (fun b ↦ (g.toLRSHom.base z : ULift.{u} (Fin m) → ℂ) (ULift.up b)) j.down := by
  rw [base_eq_eval_coordPullback, coordPullback_affineProdLift]
  obtain ⟨j⟩ := j
  induction j using Fin.addCases with
  | left a => rw [Fin.addCases_left, Fin.addCases_left, base_eq_eval_coordPullback]
  | right b => rw [Fin.addCases_right, Fin.addCases_right, base_eq_eval_coordPullback]

/-! ### The open of `ℂ^(n+m)` that a pair of opens cuts out -/

/-- **The open of `ℂ^(n+m)` at which a pair of opens, one of `ℂ^n` and one of `ℂ^m`, cuts out
their product**: the meet of the preimages of the two under the two coordinate projections.

Being a meet of two preimages of opens under continuous maps, it is open with no argument, which
is why this is a definition and not a construction with a proof obligation. -/
def affineProdOpens (V : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
    (W : (AnalyticSpace.complexAffineSpace.{u} m).Opens) :
    (AnalyticSpace.complexAffineSpace.{u} (n + m)).Opens :=
  (Opens.map (affineProdFst.{u} n m).toLRSHom.base).obj V ⊓
    (Opens.map (affineProdSnd.{u} n m).toLRSHom.base).obj W

variable (V : (AnalyticSpace.complexAffineSpace.{u} n).Opens)
  (W : (AnalyticSpace.complexAffineSpace.{u} m).Opens)

/-- **A point of `ℂ^(n+m)` lies in `ComplexAnalytic.AnalyticSpace.affineProdOpens V W` exactly
when its two projections lie in `V` and in `W`.**

`Iff.rfl`, the definition being that meet; it is stated so that a caller can cite the
characterisation rather than unfold the definition, and so that
`ComplexAnalytic.AnalyticSpace.base_affineProdFst` and
`ComplexAnalytic.AnalyticSpace.base_affineProdSnd` can be applied to it coordinatewise. -/
theorem mem_affineProdOpens_iff (w : AnalyticSpace.complexAffineSpace.{u} (n + m)) :
    w ∈ affineProdOpens.{u} V W ↔
      (affineProdFst.{u} n m).toLRSHom.base w ∈ V ∧
        (affineProdSnd.{u} n m).toLRSHom.base w ∈ W :=
  Iff.rfl

/-! ### The two legs -/

/-- **The first leg `ℂ^(n+m)|affineProdOpens V W ⟶ ℂ^n|V`**: the inclusion followed by the first
projection, factored through `V`.

The range condition is the first component of the meet, and it is available on the point itself:
a point of `ComplexAnalytic.AnalyticSpace.restrict` at an open carries its membership in that
open, and here that membership *is* the pair of conditions. -/
def affineProdOpensFst :
    (AnalyticSpace.complexAffineSpace.{u} (n + m)).restrict (affineProdOpens.{u} V W) ⟶
      (AnalyticSpace.complexAffineSpace.{u} n).restrict V :=
  liftRestrict ((AnalyticSpace.complexAffineSpace.{u} (n + m)).ofRestrict
      (affineProdOpens.{u} V W) ≫ affineProdFst.{u} n m) V (by
    rintro _ ⟨p, rfl⟩
    exact p.2.1)

/-- **The second leg `ℂ^(n+m)|affineProdOpens V W ⟶ ℂ^m|W`**, by the argument
`ComplexAnalytic.AnalyticSpace.affineProdOpensFst` gives at the second component of the meet. -/
def affineProdOpensSnd :
    (AnalyticSpace.complexAffineSpace.{u} (n + m)).restrict (affineProdOpens.{u} V W) ⟶
      (AnalyticSpace.complexAffineSpace.{u} m).restrict W :=
  liftRestrict ((AnalyticSpace.complexAffineSpace.{u} (n + m)).ofRestrict
      (affineProdOpens.{u} V W) ≫ affineProdSnd.{u} n m) W (by
    rintro _ ⟨p, rfl⟩
    exact p.2.2)

/-- **The first leg is a factorisation of the inclusion followed by the first projection.**

`ComplexAnalytic.AnalyticSpace.liftRestrict_fac`. This equation, rather than
`ComplexAnalytic.AnalyticSpace.affineProdOpensFst` itself, is what the proofs of the two
triangles and of uniqueness consume: the lift is opaque and the composite is not. -/
theorem affineProdOpensFst_fac :
    affineProdOpensFst.{u} V W ≫ (AnalyticSpace.complexAffineSpace.{u} n).ofRestrict V =
      (AnalyticSpace.complexAffineSpace.{u} (n + m)).ofRestrict (affineProdOpens.{u} V W) ≫
        affineProdFst.{u} n m :=
  liftRestrict_fac _ _ _

/-- **The second leg is a factorisation of the inclusion followed by the second projection.** -/
theorem affineProdOpensSnd_fac :
    affineProdOpensSnd.{u} V W ≫ (AnalyticSpace.complexAffineSpace.{u} m).ofRestrict W =
      (AnalyticSpace.complexAffineSpace.{u} (n + m)).ofRestrict (affineProdOpens.{u} V W) ≫
        affineProdSnd.{u} n m :=
  liftRestrict_fac _ _ _

/-! ### The pair -/

variable {V W}

/-- **The morphism into `ℂ^(n+m)|affineProdOpens V W` assembled from a morphism into `ℂ^n|V` and
one into `ℂ^m|W`.**

`ComplexAnalytic.AnalyticSpace.affineProdLift` of the two composites with the inclusions, factored
through the open. The module docstring's section on the range condition says why the two `have`s
are stated in the applied form and how they are proved from the triangles of
`Oka/AnalyticSpace/AffineProduct.lean` rather than from
`ComplexAnalytic.AnalyticSpace.base_affineProdFst` and
`ComplexAnalytic.AnalyticSpace.base_affineProdSnd`.

**The two goal changes are `change` and not `show`**, and the difference is a build failure rather
than taste: the two spellings are definitionally equal and not syntactically equal, so
`linter.style.show` fires on `show` and `lake build --wfail` turns the warning into an error,
which `lake env lean` on a scratch file does not.
`ComplexAnalytic.AnalyticSpace.mono_ofRestrict` in `Oka/AnalyticSpace/OpenSubspace.lean` records
the same seam for the same reason. -/
def affineProdOpensLift {Z : AnalyticSpace.{u}}
    (a : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (b : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} m).restrict W) :
    Z ⟶ (AnalyticSpace.complexAffineSpace.{u} (n + m)).restrict (affineProdOpens.{u} V W) :=
  liftRestrict (affineProdLift.{u} (a ≫ (AnalyticSpace.complexAffineSpace.{u} n).ofRestrict V)
      (b ≫ (AnalyticSpace.complexAffineSpace.{u} m).ofRestrict W)) _ (by
    set A := a ≫ (AnalyticSpace.complexAffineSpace.{u} n).ofRestrict V with hA
    set B := b ≫ (AnalyticSpace.complexAffineSpace.{u} m).ofRestrict W with hB
    have hfst : ∀ z : Z, (affineProdFst.{u} n m).toLRSHom.base
        ((affineProdLift.{u} A B).toLRSHom.base z) = A.toLRSHom.base z := fun z ↦
      congrArg (fun φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n ↦ φ.toLRSHom.base z)
        (affineProdLift_fst.{u} A B)
    have hsnd : ∀ z : Z, (affineProdSnd.{u} n m).toLRSHom.base
        ((affineProdLift.{u} A B).toLRSHom.base z) = B.toLRSHom.base z := fun z ↦
      congrArg (fun φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m ↦ φ.toLRSHom.base z)
        (affineProdLift_snd.{u} A B)
    rintro _ ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · change (affineProdFst.{u} n m).toLRSHom.base _ ∈ V
      rw [hfst z]
      exact (a.toLRSHom.base z).2
    · change (affineProdSnd.{u} n m).toLRSHom.base _ ∈ W
      rw [hsnd z]
      exact (b.toLRSHom.base z).2)

/-- **The pair followed by the inclusion is the pair taken in `ℂ^(n+m)`.**

`ComplexAnalytic.AnalyticSpace.liftRestrict_fac` again, and it is how
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_fst` and
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_snd` reach the triangles of
`Oka/AnalyticSpace/AffineProduct.lean`. -/
theorem affineProdOpensLift_ofRestrict {Z : AnalyticSpace.{u}}
    (a : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (b : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} m).restrict W) :
    affineProdOpensLift.{u} a b ≫ (AnalyticSpace.complexAffineSpace.{u} (n + m)).ofRestrict
        (affineProdOpens.{u} V W) =
      affineProdLift.{u} (a ≫ (AnalyticSpace.complexAffineSpace.{u} n).ofRestrict V)
        (b ≫ (AnalyticSpace.complexAffineSpace.{u} m).ofRestrict W) :=
  liftRestrict_fac _ _ _

/-- **The pair followed by the first leg is the first morphism.**

Both sides are morphisms into an open subspace and
`ComplexAnalytic.AnalyticSpace.mono_ofRestrict` cancels its inclusion, after which the equation is
`ComplexAnalytic.AnalyticSpace.affineProdOpensFst_fac`,
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_ofRestrict` and
`ComplexAnalytic.AnalyticSpace.affineProdLift_fst` in that order. -/
theorem affineProdOpensLift_fst {Z : AnalyticSpace.{u}}
    (a : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (b : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} m).restrict W) :
    affineProdOpensLift.{u} a b ≫ affineProdOpensFst.{u} V W = a := by
  refine (cancel_mono ((AnalyticSpace.complexAffineSpace.{u} n).ofRestrict V)).1 ?_
  rw [Category.assoc, affineProdOpensFst_fac, ← Category.assoc,
    affineProdOpensLift_ofRestrict, affineProdLift_fst]

/-- **The pair followed by the second leg is the second morphism**, by the argument
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_fst` gives at the second leg. -/
theorem affineProdOpensLift_snd {Z : AnalyticSpace.{u}}
    (a : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (b : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} m).restrict W) :
    affineProdOpensLift.{u} a b ≫ affineProdOpensSnd.{u} V W = b := by
  refine (cancel_mono ((AnalyticSpace.complexAffineSpace.{u} m).ofRestrict W)).1 ?_
  rw [Category.assoc, affineProdOpensSnd_fac, ← Category.assoc,
    affineProdOpensLift_ofRestrict, affineProdLift_snd]

/-- **A morphism into `ℂ^(n+m)|affineProdOpens V W` is determined by its two legs.**

Two cancellations and no computation: `ComplexAnalytic.AnalyticSpace.mono_ofRestrict` reduces the
goal to an equation of morphisms into `ℂ^(n+m)`, which
`ComplexAnalytic.AnalyticSpace.hom_ext_affineProd` reduces to the two projections agreeing, and
each of those is the corresponding hypothesis pushed through
`ComplexAnalytic.AnalyticSpace.affineProdOpensFst_fac`. -/
theorem hom_ext_affineProdOpens {Z : AnalyticSpace.{u}}
    (φ ψ : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} (n + m)).restrict (affineProdOpens.{u} V W))
    (h₁ : φ ≫ affineProdOpensFst.{u} V W = ψ ≫ affineProdOpensFst.{u} V W)
    (h₂ : φ ≫ affineProdOpensSnd.{u} V W = ψ ≫ affineProdOpensSnd.{u} V W) :
    φ = ψ := by
  refine (cancel_mono ((AnalyticSpace.complexAffineSpace.{u} (n + m)).ofRestrict
    (affineProdOpens.{u} V W))).1 (hom_ext_affineProd.{u} _ _ ?_ ?_)
  · rw [Category.assoc, Category.assoc, ← affineProdOpensFst_fac, ← Category.assoc,
      ← Category.assoc, h₁]
  · rw [Category.assoc, Category.assoc, ← affineProdOpensSnd_fac, ← Category.assoc,
      ← Category.assoc, h₂]

/-! ### The open subspace at `affineProdOpens` is the binary product -/

variable (V W)

/-- **`ℂ^(n+m)|affineProdOpens V W` with its two legs, as a binary fan** over `ℂ^n|V` and
`ℂ^m|W`. -/
def binaryFanAffineProdOpens :
    BinaryFan ((AnalyticSpace.complexAffineSpace.{u} n).restrict V)
      ((AnalyticSpace.complexAffineSpace.{u} m).restrict W) :=
  BinaryFan.mk (affineProdOpensFst.{u} V W) (affineProdOpensSnd.{u} V W)

/-- **`ℂ^(n+m)|affineProdOpens V W` is the product of `ℂ^n|V` and `ℂ^m|W` in
`ComplexAnalytic.AnalyticSpace`.**

The lift is `ComplexAnalytic.AnalyticSpace.affineProdOpensLift` at the cone's two legs, the two
triangles are `ComplexAnalytic.AnalyticSpace.affineProdOpensLift_fst` and
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_snd`, and uniqueness is
`ComplexAnalytic.AnalyticSpace.hom_ext_affineProdOpens`, which asks exactly what
`CategoryTheory.Limits.BinaryFan.isLimitMk` supplies. -/
def isLimitBinaryFanAffineProdOpens : IsLimit (binaryFanAffineProdOpens.{u} V W) :=
  BinaryFan.isLimitMk (fun s ↦ affineProdOpensLift.{u} s.fst s.snd)
    (fun s ↦ affineProdOpensLift_fst.{u} s.fst s.snd)
    (fun s ↦ affineProdOpensLift_snd.{u} s.fst s.snd)
    fun _ _ h₁ h₂ ↦ hom_ext_affineProdOpens.{u} _ _
      (by rw [h₁, affineProdOpensLift_fst]) (by rw [h₂, affineProdOpensLift_snd])

/-- **The binary product of two open subspaces of complex affine spaces exists**, so
`ℂ^n|V ⨯ ℂ^m|W` is usable notation.

`CategoryTheory.Limits.HasBinaryProduct` is `Prop`-valued, so this instance loses the
identification of the product with `ℂ^(n+m)|affineProdOpens V W`;
`ComplexAnalytic.AnalyticSpace.isLimitBinaryFanAffineProdOpens` is what keeps it, and
`ComplexAnalytic.AnalyticSpace.affineProdOpensIsoProd` is that identification stated against the
notation. -/
instance hasBinaryProduct_restrict_complexAffineSpace :
    HasBinaryProduct ((AnalyticSpace.complexAffineSpace.{u} n).restrict V)
      ((AnalyticSpace.complexAffineSpace.{u} m).restrict W) :=
  ⟨⟨_, isLimitBinaryFanAffineProdOpens.{u} V W⟩⟩

/-- **The open subspace at `ComplexAnalytic.AnalyticSpace.affineProdOpens` is the categorical
product**, as an isomorphism against the `⨯` notation.

Two limits with the same diagram, so
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`. **The statement does not elaborate unless
`ComplexAnalytic.AnalyticSpace.hasBinaryProduct_restrict_complexAffineSpace` is found by instance
search**, `⨯` being notation for a `CategoryTheory.Limits.limit` that needs it; so this
declaration, and the guard on it, test that the instance is found and not merely that it
exists. -/
def affineProdOpensIsoProd :
    (AnalyticSpace.complexAffineSpace.{u} (n + m)).restrict (affineProdOpens.{u} V W) ≅
      (AnalyticSpace.complexAffineSpace.{u} n).restrict V ⨯
        (AnalyticSpace.complexAffineSpace.{u} m).restrict W :=
  (isLimitBinaryFanAffineProdOpens.{u} V W).conePointUniqueUpToIso (limit.isLimit _)

end ComplexAnalytic.AnalyticSpace
