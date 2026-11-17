/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.AffineProductOpen
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.Factorisation

/-!
# The binary product of two local models

`Oka/AnalyticSpace/AffineProductOpen.lean` makes `ℂ^(n+m)|affineProdOpens V W` the binary product
of `ℂ^n|V` and `ℂ^m|W`. That is the *ambient* object of a product of two local models, and this
file cuts the product out inside it: if `X` is cut out in `ℂ^n|V` by `f₁, …, f_k` and `Y` is cut
out in `ℂ^m|W` by `g₁, …, g_l`, then **the zero locus, inside `ℂ^(n+m)|affineProdOpens V W`, of
the `f j` pulled back along the first leg together with the `g j` pulled back along the second is
the binary product of `X` and `Y`.**

## The object costs no stalk-level work

`AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι` in
`Oka/AnalyticSpace/LocalModel.lean` gives all four fields of `ComplexAnalytic.IsCutOutBy` — closed
embedding, image, surjectivity on stalks, kernel — for an arbitrary locally ringed space and an
arbitrary finite family of global sections, and
`ComplexAnalytic.AnalyticSpace.ofCutOut` turns that datum into an analytic space carrying the
right `ℂ`-algebra structure. So the candidate product object is assembled and not constructed, and
nothing below computes a stalk. What has content is the universal property, and the universal
property is `ComplexAnalytic.IsCutOutBy.lift` in `Oka/AnalyticSpace/Factorisation.lean` used three
times: twice to build the projections and once to build the pair.

## The mapping property in the shape this file uses it

`ComplexAnalytic.IsCutOutBy.lift` and `ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` take a
morphism of *locally ringed spaces* into the ambient open subspace, together with a `ℂ`-linearity
hypothesis and the vanishing of the cutting sections. Everything this file pairs and cancels is a
morphism of *analytic spaces*, so that mapping property is repackaged at the analytic level
before the product is built: `ComplexAnalytic.AnalyticSpace.ofCutOutHom` is the closed immersion
as a morphism of analytic spaces, `ComplexAnalytic.AnalyticSpace.liftHom` is the factorisation,
and `ComplexAnalytic.AnalyticSpace.hom_ext_ofCutOut` is uniqueness. **No transport is involved**:
the `ℂ`-algebra structure `ComplexAnalytic.AnalyticSpace.ofCutOut` installs is by definition the
ambient one pulled back along the immersion, so the `ℂ`-linearity of `ofCutOutHom` is `fun _ ↦ rfl`
and the one of `liftHom` is `ComplexAnalytic.IsCutOutBy.isCLinearHom_lift` at the nose.

Those three are stated for an arbitrary closed immersion into an arbitrary `ℂ^n|V` and do not
mention the product. **Exactly one of those three has no earlier home, and it is
`ComplexAnalytic.AnalyticSpace.liftHom`**: it is built from
`ComplexAnalytic.IsCutOutBy.lift` and `ComplexAnalytic.IsCutOutBy.isCLinearHom_lift`, which arrive
in `Oka/AnalyticSpace/Factorisation.lean`, and it lands in a
`ComplexAnalytic.AnalyticSpace.restrict`, which arrives in
`Oka/AnalyticSpace/OpenSubspace.lean`. **Neither of those two files is in the other's import
closure**, so neither has both, and `ComplexAnalytic.AnalyticSpace.liftHom_comp` is forced with it.

**The section's other declarations are not forced, and their placement is a preference, which is
checkable and was checked rather than argued.** A file importing
`Oka/AnalyticSpace/OpenSubspace.lean` and nothing else takes
`ComplexAnalytic.AnalyticSpace.ofCutOutHom`,
`ComplexAnalytic.AnalyticSpace.toLRSHom_ofCutOutHom`,
`ComplexAnalytic.AnalyticSpace.pullbackΓ_ofCutOutHom_eq_zero`,
`ComplexAnalytic.AnalyticSpace.mono_ofCutOutHom` and
`ComplexAnalytic.AnalyticSpace.hom_ext_ofCutOut`, bodies unchanged, with no output at all:
`ComplexAnalytic.AnalyticSpace.ofCutOut` arrives in `Oka/AnalyticSpace/LocalModel.lean`, which
`Oka/AnalyticSpace/OpenSubspace.lean` imports, so that file has
`ComplexAnalytic.AnalyticSpace.ofCutOut` and `ComplexAnalytic.AnalyticSpace.restrict` alike, which
is all any of those names asks for. They are here so that the mapping property is stated in one
place, and because that file's subject is the open subspace where this is the mapping property of
a closed one. **That is a reason of taste and is given as one.**

**This paragraph read *"`Oka/AnalyticSpace/OpenSubspace.lean` imports
`Oka/AnalyticSpace/LocalModel.lean`, so neither of those two files has both"* until 2026-09-07.**
That import is what gives `Oka/AnalyticSpace/OpenSubspace.lean` both, so the clause was false and
the import it cited was the reason it was false.

## The vanishing condition, which is the step this file was expected to fight

`ComplexAnalytic.IsCutOutBy.lift` asks that the morphism being factored kill the cutting sections
*as a map on global sections*, and what comes free from the zero-locus datum is the vanishing of
the *pulled-back* sections. Turning one into the other is contravariant functoriality of global
sections along a composite, which is
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ_comp` in `Oka/AnalyticSpace/Basic.lean` — added there
by this branch, beside the `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` it is about. With that
lemma each of the three vanishing obligations is two rewrites and a `map_zero`; without it the
`Γ.map` spelling puts the goal outside the `instances` transparency level and every later rewrite
is rejected, which is the seam
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ`'s own docstring records.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.ofCutOutHom`: the closed immersion of
  `ComplexAnalytic.AnalyticSpace.ofCutOut` as a morphism of analytic spaces.
- `ComplexAnalytic.AnalyticSpace.liftHom`: the factorisation of a morphism of analytic spaces
  killing the cutting sections.
- `ComplexAnalytic.AnalyticSpace.prodCutFamily`: the `k + l` sections that cut the product out.
- `ComplexAnalytic.AnalyticSpace.prodCutOut`: the product object.
- `ComplexAnalytic.AnalyticSpace.prodCutOutι`: its closed immersion into
  `ℂ^(n+m)|affineProdOpens V W`.
- `ComplexAnalytic.AnalyticSpace.prodCutOutFst` and
  `ComplexAnalytic.AnalyticSpace.prodCutOutSnd`: the two projections.
- `ComplexAnalytic.AnalyticSpace.prodCutOutLift`: the pair.
- `ComplexAnalytic.AnalyticSpace.prodCutOutIsoProd`: the identification of
  `ComplexAnalytic.AnalyticSpace.prodCutOut` with the categorical product `X ⨯ Y`.

## Main results

- `ComplexAnalytic.AnalyticSpace.hom_ext_ofCutOut`: **a morphism into
  `ComplexAnalytic.AnalyticSpace.ofCutOut` is determined by its composite with the immersion**,
  which is `ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy` in cancellation form.
- `ComplexAnalytic.AnalyticSpace.isCutOutBy_prodCutFamily`: **the product object is cut out by
  `ComplexAnalytic.AnalyticSpace.prodCutFamily`**, with no proof obligation of its own.
- `ComplexAnalytic.AnalyticSpace.prodCutOutLift_fst`,
  `ComplexAnalytic.AnalyticSpace.prodCutOutLift_snd` and
  `ComplexAnalytic.AnalyticSpace.hom_ext_prodCutOut`: the two triangles and uniqueness.
- `ComplexAnalytic.AnalyticSpace.isLimitBinaryFanProdCutOut`: **the zero locus of the appended
  family is the binary product of the two local models**, and
  `ComplexAnalytic.AnalyticSpace.hasBinaryProduct_ofCutOut` is the instance.

## What is not here

* **`CategoryTheory.Limits.HasBinaryProducts ComplexAnalytic.AnalyticSpace`.** What lands here is
  the product of two objects presented as `ComplexAnalytic.AnalyticSpace.ofCutOut` — that is, of
  two *local models* — and nothing wider. A general analytic space is only locally a local model,
  and gluing the local products is a separate rung. At `8bfb421`, the commit this file first
  reached `master` in, `#synth CategoryTheory.Limits.HasBinaryProducts
  ComplexAnalytic.AnalyticSpace` fails — elaborated rather than grepped. **That clause named
  `bbbc91f` and called it this file's base until 2026-09-07.** `bbbc91f` is the base of
  `Oka/AnalyticSpace/AffineProductOpen.lean`, where it is exact; this file imports that one and
  `bbbc91f` predates it, so this file cannot be put in that tree at all and the probe cannot be
  run there.
* **Anything over a base.** Both statements here are absolute products. The fibre product over a
  common base is an equaliser inside such a product; no construction below builds an equaliser or
  bears on `CategoryTheory.Limits.HasPullback`, and `#synth
  CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` fails at that same commit.

  **It is in `Oka/AnalyticSpace/CutOutFibreProduct.lean`**, which imports this file — one edge,
  measured — and which cuts the product below down by the `p` differences of the two composites to
  `ℂ^p`, giving `CategoryTheory.Limits.HasPullback` at a cospan of local models. **The bullet is
  unchanged by that and nothing here is retired**: *below* is this file, which still builds no
  equaliser, and `#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` still
  fails at the commit that adds that file. This paragraph was added on 2026-09-07 by the push that
  added it.
* **Any description of the product on points.** The underlying set of
  `ComplexAnalytic.AnalyticSpace.prodCutOut` is the zero locus of the appended family, and no
  statement below identifies it with a set of pairs or computes the base map of either projection.
  `ComplexAnalytic.AnalyticSpace.base_affineProdFst` and its companions in
  `Oka/AnalyticSpace/AffineProductOpen.lean` are what such a statement would run on.
* **Independence of the presentation.** `ComplexAnalytic.AnalyticSpace.prodCutOut` is indexed by
  the two cutting families and not by the two spaces, and two presentations of the same local
  model give two objects, canonically isomorphic through
  `ComplexAnalytic.AnalyticSpace.prodCutOutIsoProd` at each and the universal property. Nothing
  below states that isomorphism.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

/-! ### The mapping property of `ofCutOut`, at the analytic level -/

section CutOutHom

variable {n k : ℕ} {V : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
  {M : LocallyRingedSpace.{u}}
  {i : M ⟶ (_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding}
  {f : Fin k → ((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)}

/-- **The closed immersion of `ComplexAnalytic.AnalyticSpace.ofCutOut` as a morphism of analytic
spaces.**

The `ℂ`-algebra structure `ComplexAnalytic.AnalyticSpace.ofCutOut` installs on the subspace *is*
the constants of the ambient open subspace pulled back along `i`, so the `ℂ`-linearity field is
`fun _ ↦ rfl` and no transport of algebra structures happens anywhere. -/
def ofCutOutHom (hcut : IsCutOutBy i f) :
    AnalyticSpace.ofCutOut hcut ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V :=
  ⟨i, fun _ ↦ rfl⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.ofCutOutHom` is the closed immersion it was built from. -/
@[simp]
lemma toLRSHom_ofCutOutHom (hcut : IsCutOutBy i f) :
    (ofCutOutHom hcut).toLRSHom = i := rfl

/-- **The cutting sections pull back to zero along
`ComplexAnalytic.AnalyticSpace.ofCutOutHom`**, in the `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ`
spelling.

`ComplexAnalytic.IsCutOutBy.c_app_eq_zero` says this of the underlying morphism; the two
statements are the same term, `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` being
`AlgebraicGeometry.LocallyRingedSpace.Γ.map` and
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_op` identifying that with the component of `c` at `⊤`.
Restating it is what keeps every rewrite below inside the `pullbackΓ` spelling. -/
theorem pullbackΓ_ofCutOutHom_eq_zero (hcut : IsCutOutBy i f) (j : Fin k) :
    (ofCutOutHom hcut).pullbackΓ (f j) = 0 :=
  hcut.c_app_eq_zero j

/-- **`ComplexAnalytic.AnalyticSpace.ofCutOutHom` is a monomorphism**, so it cancels.

`ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy` at the datum this immersion carries. -/
instance mono_ofCutOutHom (hcut : IsCutOutBy i f) : Mono (ofCutOutHom hcut) :=
  mono_of_isCutOutBy _ hcut

/-- **A morphism of analytic spaces into `ℂ^n|V` killing the cutting sections factors through the
subspace they cut out.**

`ComplexAnalytic.IsCutOutBy.lift` supplies the underlying morphism and
`ComplexAnalytic.IsCutOutBy.isCLinearHom_lift` supplies its `ℂ`-linearity, at the algebra
structure `ComplexAnalytic.AnalyticSpace.ofCutOut` was defined with. This is
`ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` with the datum named rather than left inside an
existential, and with the hypothesis in the `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ`
spelling. -/
def liftHom (hcut : IsCutOutBy i f) {Z : AnalyticSpace.{u}}
    (φ : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (hφ : ∀ j, φ.pullbackΓ (f j) = 0) : Z ⟶ AnalyticSpace.ofCutOut hcut :=
  ⟨hcut.lift φ.toLRSHom hφ, hcut.isCLinearHom_lift _ _ φ.isCLinear⟩

/-- **The factorisation followed by the immersion is the original morphism.**

`ComplexAnalytic.IsCutOutBy.lift_comp`, pushed up along
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`, which is faithful. This equation and
not `ComplexAnalytic.AnalyticSpace.liftHom` itself is what every proof below consumes. -/
@[simp]
lemma liftHom_comp (hcut : IsCutOutBy i f) {Z : AnalyticSpace.{u}}
    (φ : Z ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (hφ : ∀ j, φ.pullbackΓ (f j) = 0) :
    liftHom hcut φ hφ ≫ ofCutOutHom hcut = φ :=
  forgetToLocallyRingedSpace.map_injective (hcut.lift_comp φ.toLRSHom hφ)

/-- **A morphism into `ComplexAnalytic.AnalyticSpace.ofCutOut` is determined by its composite with
the immersion**, which is `ComplexAnalytic.AnalyticSpace.mono_ofCutOutHom` in the form a
cancellation argument uses. -/
theorem hom_ext_ofCutOut (hcut : IsCutOutBy i f) {Z : AnalyticSpace.{u}}
    (ψ₁ ψ₂ : Z ⟶ AnalyticSpace.ofCutOut hcut)
    (h : ψ₁ ≫ ofCutOutHom hcut = ψ₂ ≫ ofCutOutHom hcut) : ψ₁ = ψ₂ :=
  (cancel_mono (ofCutOutHom hcut)).1 h

end CutOutHom

/-! ### The family that cuts the product out, and the product object -/

section Product

variable {n m k l : ℕ}
  {V : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
  {W : (AnalyticSpace.complexAffineSpace.{u} m).Opens}
  {MX MY : LocallyRingedSpace.{u}}
  {iX : MX ⟶ (_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding}
  {iY : MY ⟶ (_root_.complexAffineSpace.{u} m).restrict W.isOpenEmbedding}

variable (f : Fin k → ((_root_.complexAffineSpace.{u} n).restrict
    V.isOpenEmbedding).presheaf.obj (op ⊤))
  (g : Fin l → ((_root_.complexAffineSpace.{u} m).restrict
    W.isOpenEmbedding).presheaf.obj (op ⊤))

/-- **The `k + l` sections of `ℂ^(n+m)|affineProdOpens V W` that cut out the product**: the `f j`
pulled back along the first leg, then the `g j` pulled back along the second.

`Fin.append` rather than a `Sum`-indexed family, because `ComplexAnalytic.IsCutOutBy` is stated
for a family indexed by a `Fin`. The two component lemmas
`ComplexAnalytic.AnalyticSpace.prodCutFamily_castAdd` and
`ComplexAnalytic.AnalyticSpace.prodCutFamily_natAdd` are what every proof below uses; the
`Fin.append` itself is not unfolded again. -/
def prodCutFamily : Fin (k + l) →
      ((_root_.complexAffineSpace.{u} (n + m)).restrict
        (affineProdOpens.{u} V W).isOpenEmbedding).presheaf.obj (op ⊤) :=
  Fin.append (fun j ↦ (affineProdOpensFst.{u} V W).pullbackΓ (f j))
    (fun j ↦ (affineProdOpensSnd.{u} V W).pullbackΓ (g j))

/-- The first `k` members of `ComplexAnalytic.AnalyticSpace.prodCutFamily` are the `f j` pulled
back along the first leg. -/
@[simp]
theorem prodCutFamily_castAdd (j : Fin k) :
    prodCutFamily.{u} f g (Fin.castAdd l j) = (affineProdOpensFst.{u} V W).pullbackΓ (f j) :=
  Fin.append_left _ _ j

/-- The last `l` members of `ComplexAnalytic.AnalyticSpace.prodCutFamily` are the `g j` pulled
back along the second leg. -/
@[simp]
theorem prodCutFamily_natAdd (j : Fin l) :
    prodCutFamily.{u} f g (Fin.natAdd k j) = (affineProdOpensSnd.{u} V W).pullbackΓ (g j) :=
  Fin.append_right _ _ j

/-- **The zero locus of `ComplexAnalytic.AnalyticSpace.prodCutFamily` is cut out by it.**

`AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι` holds for an arbitrary
locally ringed space and an arbitrary finite family, so this is an instantiation and not an
argument: all four fields of `ComplexAnalytic.IsCutOutBy` were discharged once in
`Oka/Geometry/RingedSpace/ZeroLocus.lean`. This is the measurement that makes the product object
free. -/
theorem isCutOutBy_prodCutFamily :
    IsCutOutBy (((_root_.complexAffineSpace.{u} (n + m)).restrict
        (affineProdOpens.{u} V W).isOpenEmbedding).zeroLocusSubspaceι (prodCutFamily.{u} f g))
      (prodCutFamily.{u} f g) :=
  _root_.AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι _ _

/-- **The product of the local model cut out by `f` and the one cut out by `g`**: the zero locus,
inside `ℂ^(n+m)|affineProdOpens V W`, of the two families pulled back along the two legs.

It is indexed by the two *families* and not by the two spaces, because that is what the object
depends on: neither `iX` nor `iY` appears, and no cut-out datum is needed to build it.
`ComplexAnalytic.AnalyticSpace.prodCutOutFst` and `ComplexAnalytic.AnalyticSpace.prodCutOutSnd`
are where the two immersions enter. -/
def prodCutOut : AnalyticSpace.{u} :=
  AnalyticSpace.ofCutOut (isCutOutBy_prodCutFamily.{u} f g)

/-- **The closed immersion of the product into the ambient open subspace of `ℂ^(n+m)`.** -/
def prodCutOutι : prodCutOut.{u} f g ⟶
    (AnalyticSpace.complexAffineSpace.{u} (n + m)).restrict (affineProdOpens.{u} V W) :=
  ofCutOutHom (isCutOutBy_prodCutFamily.{u} f g)

variable {f g}

/-! ### The two projections -/

set_option backward.isDefEq.respectTransparency false in
/-- **The `f j` pull back to zero along the immersion of the product followed by the first leg.**

Two rewrites: `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ_comp` splits the composite, and
`ComplexAnalytic.AnalyticSpace.prodCutFamily_castAdd` recognises the inner pullback as a member of
the cutting family, at which point
`ComplexAnalytic.AnalyticSpace.pullbackΓ_ofCutOutHom_eq_zero` applies. This is the obligation the
filing of this issue named as the one open step, and it is the whole of it. -/
theorem pullbackΓ_prodCutOutι_fst (j : Fin k) :
    (prodCutOutι.{u} f g ≫ affineProdOpensFst.{u} V W).pullbackΓ (f j) = 0 := by
  rw [Hom.pullbackΓ_comp, ← prodCutFamily_castAdd.{u} f g j]
  exact pullbackΓ_ofCutOutHom_eq_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The `g j` pull back to zero along the immersion of the product followed by the second
leg**, by the argument `ComplexAnalytic.AnalyticSpace.pullbackΓ_prodCutOutι_fst` gives at
`ComplexAnalytic.AnalyticSpace.prodCutFamily_natAdd`. -/
theorem pullbackΓ_prodCutOutι_snd (j : Fin l) :
    (prodCutOutι.{u} f g ≫ affineProdOpensSnd.{u} V W).pullbackΓ (g j) = 0 := by
  rw [Hom.pullbackΓ_comp, ← prodCutFamily_natAdd.{u} f g j]
  exact pullbackΓ_ofCutOutHom_eq_zero _ _

/-- **The first projection of the product onto the local model cut out by `f`.**

The immersion of the product followed by the first leg of the ambient product kills the `f j`, so
`ComplexAnalytic.AnalyticSpace.liftHom` factors it through the immersion of that local model. -/
def prodCutOutFst (hX : IsCutOutBy iX f) (g : Fin l → ((_root_.complexAffineSpace.{u} m).restrict
    W.isOpenEmbedding).presheaf.obj (op ⊤)) :
    prodCutOut.{u} f g ⟶ AnalyticSpace.ofCutOut hX :=
  liftHom hX (prodCutOutι.{u} f g ≫ affineProdOpensFst.{u} V W) pullbackΓ_prodCutOutι_fst

/-- **The second projection of the product onto the local model cut out by `g`.** -/
def prodCutOutSnd (f : Fin k → ((_root_.complexAffineSpace.{u} n).restrict
    V.isOpenEmbedding).presheaf.obj (op ⊤)) (hY : IsCutOutBy iY g) :
    prodCutOut.{u} f g ⟶ AnalyticSpace.ofCutOut hY :=
  liftHom hY (prodCutOutι.{u} f g ≫ affineProdOpensSnd.{u} V W) pullbackΓ_prodCutOutι_snd

/-- **The first projection is a factorisation of the immersion followed by the first leg.**

`ComplexAnalytic.AnalyticSpace.liftHom_comp`. As in `Oka/AnalyticSpace/AffineProductOpen.lean`,
this equation and not the projection is what the triangles and uniqueness run on: the
factorisation is opaque and the composite is not. -/
theorem prodCutOutFst_fac (hX : IsCutOutBy iX f) :
    prodCutOutFst.{u} hX g ≫ ofCutOutHom hX =
      prodCutOutι.{u} f g ≫ affineProdOpensFst.{u} V W :=
  liftHom_comp _ _ _

/-- **The second projection is a factorisation of the immersion followed by the second leg.** -/
theorem prodCutOutSnd_fac (hY : IsCutOutBy iY g) :
    prodCutOutSnd.{u} f hY ≫ ofCutOutHom hY =
      prodCutOutι.{u} f g ≫ affineProdOpensSnd.{u} V W :=
  liftHom_comp _ _ _

/-! ### The pair, uniqueness, and the limit -/

variable {Z : AnalyticSpace.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **The pair of two morphisms into the two local models kills the whole cutting family.**

`Fin.addCases` splits the family; on each half
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ_comp` turns the pulled-back section into a pullback
along the pair *followed by* the corresponding leg, which
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_fst` identifies with the corresponding
morphism, and that one kills the section by
`ComplexAnalytic.AnalyticSpace.pullbackΓ_ofCutOutHom_eq_zero`. The final step is `map_zero`: the
pullback of `0` is `0` because pulling back is a ring homomorphism, and none of this touches a
point or a stalk. -/
theorem pullbackΓ_affineProdOpensLift_prodCutFamily (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g)
    (a : Z ⟶ AnalyticSpace.ofCutOut hX) (b : Z ⟶ AnalyticSpace.ofCutOut hY) (j : Fin (k + l)) :
    (affineProdOpensLift.{u} (a ≫ ofCutOutHom hX) (b ≫ ofCutOutHom hY)).pullbackΓ
      (prodCutFamily.{u} f g j) = 0 := by
  induction j using Fin.addCases with
  | left j =>
    rw [prodCutFamily_castAdd, ← Hom.pullbackΓ_comp, affineProdOpensLift_fst,
      Hom.pullbackΓ_comp, pullbackΓ_ofCutOutHom_eq_zero]
    exact map_zero _
  | right j =>
    rw [prodCutFamily_natAdd, ← Hom.pullbackΓ_comp, affineProdOpensLift_snd,
      Hom.pullbackΓ_comp, pullbackΓ_ofCutOutHom_eq_zero]
    exact map_zero _

/-- **The morphism into the product assembled from a morphism into each factor.**

`ComplexAnalytic.AnalyticSpace.affineProdOpensLift` of the two composites with the two immersions,
factored through the product by `ComplexAnalytic.AnalyticSpace.liftHom`. -/
def prodCutOutLift (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g)
    (a : Z ⟶ AnalyticSpace.ofCutOut hX) (b : Z ⟶ AnalyticSpace.ofCutOut hY) :
    Z ⟶ prodCutOut.{u} f g :=
  liftHom (isCutOutBy_prodCutFamily.{u} f g)
    (affineProdOpensLift.{u} (a ≫ ofCutOutHom hX) (b ≫ ofCutOutHom hY))
    (pullbackΓ_affineProdOpensLift_prodCutFamily hX hY a b)

/-- **The pair followed by the immersion of the product is the pair taken in the ambient open
subspace of `ℂ^(n+m)`**, which is how the two triangles reach
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_fst` and
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_snd`. -/
theorem prodCutOutLift_ι (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g)
    (a : Z ⟶ AnalyticSpace.ofCutOut hX) (b : Z ⟶ AnalyticSpace.ofCutOut hY) :
    prodCutOutLift hX hY a b ≫ prodCutOutι.{u} f g =
      affineProdOpensLift.{u} (a ≫ ofCutOutHom hX) (b ≫ ofCutOutHom hY) :=
  liftHom_comp _ _ _

/-- **The pair followed by the first projection is the first morphism.**

Both sides land in a subspace cut out by `f`, so
`ComplexAnalytic.AnalyticSpace.hom_ext_ofCutOut` cancels its immersion; after that the equation is
`ComplexAnalytic.AnalyticSpace.prodCutOutFst_fac`,
`ComplexAnalytic.AnalyticSpace.prodCutOutLift_ι` and
`ComplexAnalytic.AnalyticSpace.affineProdOpensLift_fst` in that order. -/
theorem prodCutOutLift_fst (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g)
    (a : Z ⟶ AnalyticSpace.ofCutOut hX) (b : Z ⟶ AnalyticSpace.ofCutOut hY) :
    prodCutOutLift hX hY a b ≫ prodCutOutFst.{u} hX g = a := by
  refine hom_ext_ofCutOut hX _ _ ?_
  rw [Category.assoc, prodCutOutFst_fac, ← Category.assoc, prodCutOutLift_ι,
    affineProdOpensLift_fst]

/-- **The pair followed by the second projection is the second morphism**, by the argument
`ComplexAnalytic.AnalyticSpace.prodCutOutLift_fst` gives at the second leg. -/
theorem prodCutOutLift_snd (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g)
    (a : Z ⟶ AnalyticSpace.ofCutOut hX) (b : Z ⟶ AnalyticSpace.ofCutOut hY) :
    prodCutOutLift hX hY a b ≫ prodCutOutSnd.{u} f hY = b := by
  refine hom_ext_ofCutOut hY _ _ ?_
  rw [Category.assoc, prodCutOutSnd_fac, ← Category.assoc, prodCutOutLift_ι,
    affineProdOpensLift_snd]

/-- **A morphism into the product is determined by its composite with the immersion**, which is
`ComplexAnalytic.AnalyticSpace.hom_ext_ofCutOut` at the product's own cut-out datum, restated so
that the goal is phrased in `ComplexAnalytic.AnalyticSpace.prodCutOutι` and the rewrites of
`ComplexAnalytic.AnalyticSpace.hom_ext_prodCutOut` fire on it. -/
theorem hom_ext_prodCutOutι (φ ψ : Z ⟶ prodCutOut.{u} f g)
    (h : φ ≫ prodCutOutι.{u} f g = ψ ≫ prodCutOutι.{u} f g) : φ = ψ :=
  hom_ext_ofCutOut _ _ _ h

/-- **A morphism into the product is determined by its two projections.**

Three cancellations and no computation: `ComplexAnalytic.AnalyticSpace.hom_ext_prodCutOutι`
reduces the goal to an equation of morphisms into `ℂ^(n+m)|affineProdOpens V W`, which
`ComplexAnalytic.AnalyticSpace.hom_ext_affineProdOpens` reduces to the two legs agreeing, and each
of those is the corresponding hypothesis pushed through
`ComplexAnalytic.AnalyticSpace.prodCutOutFst_fac`. -/
theorem hom_ext_prodCutOut (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g)
    (φ ψ : Z ⟶ prodCutOut.{u} f g)
    (h₁ : φ ≫ prodCutOutFst.{u} hX g = ψ ≫ prodCutOutFst.{u} hX g)
    (h₂ : φ ≫ prodCutOutSnd.{u} f hY = ψ ≫ prodCutOutSnd.{u} f hY) : φ = ψ := by
  refine hom_ext_prodCutOutι _ _ (hom_ext_affineProdOpens.{u} _ _ ?_ ?_)
  · rw [Category.assoc, Category.assoc, ← prodCutOutFst_fac hX, ← Category.assoc,
      ← Category.assoc, h₁]
  · rw [Category.assoc, Category.assoc, ← prodCutOutSnd_fac hY, ← Category.assoc,
      ← Category.assoc, h₂]

variable (f g)

/-- **The product with its two projections, as a binary fan** over the two local models. -/
def binaryFanProdCutOut (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g) :
    BinaryFan (AnalyticSpace.ofCutOut hX) (AnalyticSpace.ofCutOut hY) :=
  BinaryFan.mk (prodCutOutFst.{u} hX g) (prodCutOutSnd.{u} f hY)

/-- **The zero locus of the appended family is the binary product of the two local models in
`ComplexAnalytic.AnalyticSpace`.**

The lift is `ComplexAnalytic.AnalyticSpace.prodCutOutLift` at the cone's two legs, the two
triangles are `ComplexAnalytic.AnalyticSpace.prodCutOutLift_fst` and
`ComplexAnalytic.AnalyticSpace.prodCutOutLift_snd`, and uniqueness is
`ComplexAnalytic.AnalyticSpace.hom_ext_prodCutOut`, which asks exactly what
`CategoryTheory.Limits.BinaryFan.isLimitMk` supplies. -/
def isLimitBinaryFanProdCutOut (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g) :
    IsLimit (binaryFanProdCutOut.{u} f g hX hY) :=
  BinaryFan.isLimitMk (fun s ↦ prodCutOutLift hX hY s.fst s.snd)
    (fun s ↦ prodCutOutLift_fst hX hY s.fst s.snd)
    (fun s ↦ prodCutOutLift_snd hX hY s.fst s.snd)
    fun _ _ h₁ h₂ ↦ hom_ext_prodCutOut hX hY _ _
      (by rw [h₁, prodCutOutLift_fst]) (by rw [h₂, prodCutOutLift_snd])

/-- **The binary product of two local models exists**, so `X ⨯ Y` is usable notation at a pair of
them.

`CategoryTheory.Limits.HasBinaryProduct` is `Prop`-valued, so this instance loses the
identification of the product with the zero locus;
`ComplexAnalytic.AnalyticSpace.isLimitBinaryFanProdCutOut` is what keeps it, and
`ComplexAnalytic.AnalyticSpace.prodCutOutIsoProd` is that identification stated against the
notation. -/
instance hasBinaryProduct_ofCutOut (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g) :
    HasBinaryProduct (AnalyticSpace.ofCutOut hX) (AnalyticSpace.ofCutOut hY) :=
  ⟨⟨_, isLimitBinaryFanProdCutOut.{u} f g hX hY⟩⟩

/-- **The zero locus of the appended family is the categorical product**, as an isomorphism
against the `⨯` notation.

Two limits with the same diagram, so
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`. **The statement does not elaborate unless
`ComplexAnalytic.AnalyticSpace.hasBinaryProduct_ofCutOut` is found by instance search**, `⨯` being
notation for a `CategoryTheory.Limits.limit` that needs it; so this declaration, and the guard on
it, test that the instance is found and not merely that it exists. -/
def prodCutOutIsoProd (hX : IsCutOutBy iX f) (hY : IsCutOutBy iY g) :
    prodCutOut.{u} f g ≅ AnalyticSpace.ofCutOut hX ⨯ AnalyticSpace.ofCutOut hY :=
  (isLimitBinaryFanProdCutOut.{u} f g hX hY).conePointUniqueUpToIso (limit.isLimit _)

end Product

end ComplexAnalytic.AnalyticSpace
