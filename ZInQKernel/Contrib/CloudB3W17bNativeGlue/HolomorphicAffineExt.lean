import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.Scheme
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Holomorphic maps into analytified affine schemes: extensionality and open lifting

Everything here is stated against the genuine Oka analytification
(`ComplexAnalytic.analytification`, `analytificationHomEquiv`, `analytificationπ`)
and the genuine Γ–Spec adjunction.  No algebraicity, comparison or gluing
compatibility of any map is assumed.

* `lrsHom_ext_of_isAffine`: a morphism of locally ringed spaces into an affine
  scheme is determined by its pullback of global regular functions.
* `analytification_hom_ext_of_gamma`: two analytic morphisms into `V^an`
  (`V` affine, locally of finite type over `ℂ`) are equal as soon as their
  comparison maps `Z ⟶ V` pull back `Γ(V, ⊤)` by the same ring homomorphism.
  This is the faithfulness of the actual universal property composed with the
  Γ–Spec faithfulness above.
* `restrictTopValue`, `restrictTopValue_injective`: a global section of the
  restriction of Oka's `ℂⁿ` to an open `U` is a literal holomorphic function
  on `U`; two sections with the same values are equal (function extensionality).
* `analytification_hom_ext_of_values`: with `ev := restrictTopValue n U`, equal
  literal pointwise values of all pulled-back regular functions force equality of
  the analytic morphisms out of the Euclidean source.
* `exists_lift_analytification_of_range`,
  `analytification_map_cancel_of_isOpenImmersion`: an analytic morphism into
  `X^an` whose comparison map lands in an open subscheme `W ⊆ X` factors,
  uniquely, through `W^an ⟶ X^an`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bNativeGlue

universe u

/-! ### Γ–Spec faithfulness for affine targets -/

/-- Morphisms of locally ringed spaces into an affine scheme are determined by their
pullback of global regular functions (naturality of the Γ–Spec unit, and the unit is an
isomorphism at an affine scheme). -/
theorem lrsHom_ext_of_isAffine (V : Scheme.{u}) [IsAffine V] {Z : LocallyRingedSpace.{u}}
    (f g : Z ⟶ V.toLocallyRingedSpace)
    (h : (LocallyRingedSpace.Γ.map f.op).hom = (LocallyRingedSpace.Γ.map g.op).hom) :
    f = g := by
  let e := asIso V.toSpecΓ
  have H : f ≫ e.hom.toLRSHom = g ≫ e.hom.toLRSHom :=
    (LocallyRingedSpace.toΓSpec_naturality f).trans
      ((congrArg (fun μ => Z.toSpecOfAlgMap μ) h).trans
        (LocallyRingedSpace.toΓSpec_naturality g).symm)
  have he : e.hom.toLRSHom ≫ e.inv.toLRSHom = 𝟙 _ :=
    congrArg Scheme.Hom.toLRSHom e.hom_inv_id
  have HH := congrArg (fun m => m ≫ e.inv.toLRSHom) H
  simpa only [Category.assoc, he, Category.comp_id] using HH

/-! ### Faithfulness through the actual analytification universal property -/

/-- **Contract 1, Γ form.** Two analytic morphisms into the analytification of an affine
scheme locally of finite type over `ℂ` are equal when their actual comparison maps pull
back `Γ(V, ⊤)` by the same ring homomorphism. -/
theorem analytification_hom_ext_of_gamma {Z : AnalyticSpace.{u}} {X : SchemeLFTℂ.{u}}
    [IsAffine X.obj.left] (f g : Z ⟶ analytification.obj X)
    (h : (LocallyRingedSpace.Γ.map ((f.toLRSHom ≫ (analytificationπ X).left).op)).hom =
      (LocallyRingedSpace.Γ.map ((g.toLRSHom ≫ (analytificationπ X).left).op)).hom) :
    f = g := by
  apply (analytificationHomEquiv Z X).injective
  rw [analytificationHomEquiv_apply, analytificationHomEquiv_apply]
  apply Over.OverMorphism.ext
  exact lrsHom_ext_of_isAffine X.obj.left _ _ h

/-- **Contract 1, value form.** If the global sections of `Z` are detected by an injective
evaluation `ev`, then equal values of every pulled-back regular function force equality. -/
theorem analytification_hom_ext_of_values {Z : AnalyticSpace.{u}} {X : SchemeLFTℂ.{u}}
    [IsAffine X.obj.left] {S : Type*} (ev : Z.presheaf.obj (op ⊤) → S → ℂ)
    (hev : Function.Injective ev) (f g : Z ⟶ analytification.obj X)
    (h : ∀ (r : Γ(X.obj.left, ⊤)) (s : S),
      ev ((LocallyRingedSpace.Γ.map ((f.toLRSHom ≫ (analytificationπ X).left).op)).hom r) s =
        ev ((LocallyRingedSpace.Γ.map ((g.toLRSHom ≫ (analytificationπ X).left).op)).hom r) s) :
    f = g :=
  analytification_hom_ext_of_gamma f g (RingHom.ext fun r => hev (funext (h r)))

/-! ### Global sections of an open of `ℂⁿ` are literal functions -/

/-- A point of `U` lies in the image of the top open of `ℂⁿ|U`. -/
theorem mem_isOpenEmbedding_functor_top (n : ℕ) (U : Opens (complexAffineSpace.{u} n))
    (w : U) : (w : complexAffineSpace.{u} n) ∈ U.isOpenEmbedding.functor.obj ⊤ :=
  ⟨w, trivial, rfl⟩

/-- The literal value at a point `w ∈ U` of a global section of Oka's `ℂⁿ` restricted to the
open `U`: the section is an element of `OkaRing` of the image of the top open. -/
def restrictTopValue (n : ℕ) (U : Opens (complexAffineSpace.{u} n))
    (s : ((complexAffineSpace.{u} n).restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
    (w : U) : ℂ :=
  OkaRing.toFun (U.isOpenEmbedding.functor.obj ⊤) s
    ⟨(w : complexAffineSpace.{u} n), mem_isOpenEmbedding_functor_top n U w⟩

/-- **Function extensionality for sections of an open of `ℂⁿ`.** -/
theorem restrictTopValue_injective (n : ℕ) (U : Opens (complexAffineSpace.{u} n)) :
    Function.Injective (restrictTopValue.{u} n U) := by
  intro s t h
  apply OkaRing.ext
  funext y
  obtain ⟨(w : U), -, hw⟩ := y.2
  have hy : y = ⟨(w : complexAffineSpace.{u} n), mem_isOpenEmbedding_functor_top n U w⟩ :=
    Subtype.ext hw.symm
  rw [hy]
  exact congrFun h w

/-! ### Lifting through the analytification of an open subscheme -/

/-- **Open lifting.** An analytic morphism into `X^an` whose actual comparison map lands in
the image of an open immersion `W ⟶ X` factors through `W^an ⟶ X^an`. -/
theorem exists_lift_analytification_of_range {Z : AnalyticSpace.{u}} {X W : SchemeLFTℂ.{u}}
    (ι : W ⟶ X) [IsOpenImmersion ι.hom.left] (f : Z ⟶ analytification.obj X)
    (hf : Set.range (f.toLRSHom ≫ (analytificationπ X).left).base ⊆
      Set.range ι.hom.left.base) :
    ∃ f' : Z ⟶ analytification.obj W, f' ≫ analytification.map ι = f := by
  have : LocallyRingedSpace.IsOpenImmersion ι.hom.left.toLRSHom := ‹IsOpenImmersion ι.hom.left›
  let c := f.toLRSHom ≫ (analytificationπ X).left
  let l := LocallyRingedSpace.IsOpenImmersion.lift ι.hom.left.toLRSHom c hf
  have hl : l ≫ ι.hom.left.toLRSHom = c := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hc : c ≫ X.obj.hom.toLRSHom = Z.toSpecℂ := by
    have h0 := Over.w (analytificationHomEquiv Z X f)
    rw [analytificationHomEquiv_apply] at h0
    exact h0
  have hw : ι.hom.left ≫ X.obj.hom = W.obj.hom := Over.w ι.hom
  have hover : l ≫ (schemeToOverSpec.obj W.obj).hom = (AnalyticSpace.toOverSpec.obj Z).hom := by
    change l ≫ W.obj.hom.toLRSHom = Z.toSpecℂ
    rw [← hw, Scheme.Hom.comp_toLRSHom, ← Category.assoc, hl]
    exact hc
  refine ⟨(analytificationHomEquiv Z W).symm (Over.homMk l hover), ?_⟩
  apply (analytificationHomEquiv Z X).injective
  rw [analytificationHomEquiv_apply, Functor.map_comp, Category.assoc,
    analytificationπ_naturality, ← Category.assoc, ← analytificationHomEquiv_apply,
    Equiv.apply_symm_apply, analytificationHomEquiv_apply]
  apply Over.OverMorphism.ext
  exact hl

/-- **Uniqueness of the open lift.** Composition with `W^an ⟶ X^an`, for an open immersion
`W ⟶ X`, is injective on analytic morphisms. -/
theorem analytification_map_cancel_of_isOpenImmersion {Z : AnalyticSpace.{u}}
    {X W : SchemeLFTℂ.{u}} (ι : W ⟶ X) [IsOpenImmersion ι.hom.left]
    (f g : Z ⟶ analytification.obj W)
    (h : f ≫ analytification.map ι = g ≫ analytification.map ι) : f = g := by
  have : LocallyRingedSpace.IsOpenImmersion ι.hom.left.toLRSHom := ‹IsOpenImmersion ι.hom.left›
  have h' := congrArg (analytificationHomEquiv Z X) h
  simp only [analytificationHomEquiv_apply, Functor.map_comp, Category.assoc,
    analytificationπ_naturality] at h'
  have h'' : (f.toLRSHom ≫ (analytificationπ W).left) ≫ ι.hom.left.toLRSHom =
      (g.toLRSHom ≫ (analytificationπ W).left) ≫ ι.hom.left.toLRSHom :=
    congrArg CommaMorphism.left h'
  apply (analytificationHomEquiv Z W).injective
  rw [analytificationHomEquiv_apply, analytificationHomEquiv_apply]
  apply Over.OverMorphism.ext
  exact (cancel_mono ι.hom.left.toLRSHom).1 h''

/-- **Contract 1 through an affine open.** Two analytic morphisms into `X^an` that factor
through `W^an` for an affine open subscheme `W ⟶ X` are equal when the factorisations pull
back `Γ(W, ⊤)` with the same literal values. -/
theorem analytification_hom_ext_through_affine_open {Z : AnalyticSpace.{u}}
    {X W : SchemeLFTℂ.{u}} (ι : W ⟶ X) [IsAffine W.obj.left]
    {S : Type*} (ev : Z.presheaf.obj (op ⊤) → S → ℂ) (hev : Function.Injective ev)
    (f g : Z ⟶ analytification.obj X) (f' g' : Z ⟶ analytification.obj W)
    (hf : f' ≫ analytification.map ι = f) (hg : g' ≫ analytification.map ι = g)
    (h : ∀ (r : Γ(W.obj.left, ⊤)) (s : S),
      ev ((LocallyRingedSpace.Γ.map ((f'.toLRSHom ≫ (analytificationπ W).left).op)).hom r) s =
        ev ((LocallyRingedSpace.Γ.map ((g'.toLRSHom ≫ (analytificationπ W).left).op)).hom r) s) :
    f = g := by
  rw [← hf, ← hg, analytification_hom_ext_of_values ev hev f' g' h]

end ZInQ.Contrib.CloudB3W17bNativeGlue
