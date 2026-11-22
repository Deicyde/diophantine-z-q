import ZInQKernel.Contrib.CloudB3W17bNativeGlue.HolomorphicAffineExt
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicResidueNaturality
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicOpenValues
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.Glue

/-!
# Rigidity of analytic maps into analytifications, and gluing along source charts

All statements use the genuine Oka analytification universal property, the genuine
Γ–Spec adjunction and the (already proved, imported read-only) intrinsic residue
evaluation of analytic stalks.  No algebraicity, GAGA, comparison-model or
gluing-compatibility statement about any map is assumed.

* `gamma_eq_of_base_eq`, `analytification_hom_ext_of_base_affine`: for a source
  whose global sections are detected by their intrinsic values, two analytic maps
  into an affine `V^an` with the same comparison points are equal.  The kernel of
  "pull back, then evaluate at `z`" is the comparison prime of the point, and
  `ℂ`-linearity is read off the actual `Spec ℂ`-structure of the comparison maps.
* `PointwiseReduced`: sections all of whose intrinsic values vanish have zero
  germs.  Proved for the genuine Euclidean opens (`euclideanOpen_pointwiseReduced`,
  literal holomorphic functions), inherited by open subspaces, and transported
  along any analytic morphism injective on a stalk (in particular isomorphisms and
  open inclusions).
* `analytification_hom_ext_of_base`: for a pointwise-reduced source, two analytic
  maps into ANY `X^an` with the same comparison points are equal (open lifting
  into affine opens of `X` + `hom_ext_of_opens`).
* `chartGlue`: given an actual open cover `M i` of an analytic space `X`, actual
  isomorphisms `X|M i ≅ Z i` onto pointwise-reduced spaces (e.g. Euclidean opens)
  and actual analytic maps `β i : Z i ⟶ Y^an` realising one point map
  `P : X → Y` through the charts, the maps glue (by the actual
  `glueMorphismsOfOpens`) to a unique analytic `X ⟶ Y^an` realising `P`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic IsLocalRing
open ZInQ.Contrib.CloudB3W17bOkaComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bNativeGlue

universe u

/-! ### Comparison maps -/

/-- The actual comparison map of an analytic morphism into an analytification is over `Spec ℂ`. -/
theorem comparison_over {Z : AnalyticSpace.{u}} {X : SchemeLFTℂ.{u}}
    (f : Z ⟶ analytification.obj X) :
    (f.toLRSHom ≫ (analytificationπ X).left) ≫ X.obj.hom.toLRSHom = Z.toSpecℂ := by
  have h0 := Over.w (analytificationHomEquiv Z X f)
  rw [analytificationHomEquiv_apply] at h0
  exact h0

/-- The comparison map of `f' ≫ analytification.map ι` is that of `f'` followed by `ι`. -/
theorem comparison_comp_map {Z : AnalyticSpace.{u}} {X W : SchemeLFTℂ.{u}} (ι : W ⟶ X)
    (f' : Z ⟶ analytification.obj W) :
    (f' ≫ analytification.map ι).toLRSHom ≫ (analytificationπ X).left =
      (f'.toLRSHom ≫ (analytificationπ W).left) ≫ ι.hom.left.toLRSHom := by
  have hn : (analytification.map ι).toLRSHom ≫ (analytificationπ X).left =
      (analytificationπ W).left ≫ ι.hom.left.toLRSHom :=
    congrArg CommaMorphism.left (analytificationπ_naturality ι)
  change f'.toLRSHom ≫ (analytification.map ι).toLRSHom ≫ (analytificationπ X).left = _
  rw [hn, Category.assoc]

/-- Pulling a global section of `Spec R` (the adjunction counit image of `r`) back along
`toSpecOfAlgMap μ` gives `μ r`: the triangle identity of the actual Γ–Spec adjunction. -/
theorem gamma_toSpecOfAlgMap_counit (Z : LocallyRingedSpace.{u}) {R : Type u} [CommRing R]
    (μ : R →+* Z.presheaf.obj (op ⊤)) (r : R) :
    (LocallyRingedSpace.Γ.map (Z.toSpecOfAlgMap μ).op).hom
      ((ΓSpec.locallyRingedSpaceAdjunction.counit.app (op (CommRingCat.of R))).unop.hom r) =
      μ r := by
  have h := (ΓSpec.locallyRingedSpaceAdjunction.homEquiv Z (op (CommRingCat.of R))).symm_apply_apply
    (op (CommRingCat.ofHom μ))
  rw [Adjunction.homEquiv_counit] at h
  exact congrArg (fun m : (LocallyRingedSpace.Γ.rightOp.obj Z ⟶ op (CommRingCat.of R)) =>
    m.unop.hom r) h

/-- Membership in the comparison prime: `r` lies in the prime of `a z` (seen in
`Spec Γ(Y, ⊤)`) iff the germ at `z` of its pullback is not a unit. -/
theorem mem_comp_toΓSpec_base_asIdeal {Z Y : LocallyRingedSpace.{u}} (a : Z ⟶ Y) (z : Z)
    (r : Y.presheaf.obj (op ⊤)) :
    r ∈ ((a ≫ Y.toΓSpec).base z).asIdeal ↔
      Z.presheaf.Γgerm z ((LocallyRingedSpace.Γ.map a.op).hom r) ∈
        maximalIdeal (Z.presheaf.stalk z) := by
  rw [LocallyRingedSpace.toΓSpec_naturality]
  exact Iff.rfl

/-! ### Rigidity for affine targets -/

/-- Global sections are detected by their intrinsic values. -/
def GlobalPointwiseReduced (Z : AnalyticSpace.{0}) : Prop :=
  ∀ s : Z.presheaf.obj (op ⊤), (∀ z : Z, intrinsicEval Z (U := ⊤) z trivial s = 0) → s = 0

/-- **Same points force the same Γ pullback.** Two `ℂ`-linear (via `κ`) morphisms from a
source with value-detected global sections into a scheme, with the same underlying point
map, pull back global regular functions identically. -/
theorem gamma_eq_of_base_eq {Z : AnalyticSpace.{0}} (hZ : GlobalPointwiseReduced Z)
    {Y : Scheme.{0}} (a b : Z.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace)
    (κ : ℂ → Y.presheaf.obj (op ⊤))
    (hκa : ∀ c, (LocallyRingedSpace.Γ.map a.op).hom (κ c) = Z.algebraMap c)
    (hκb : ∀ c, (LocallyRingedSpace.Γ.map b.op).hom (κ c) = Z.algebraMap c)
    (hab : ∀ z, a.base z = b.base z) :
    (LocallyRingedSpace.Γ.map a.op).hom = (LocallyRingedSpace.Γ.map b.op).hom := by
  refine RingHom.ext fun (r : Y.presheaf.obj (op ⊤)) => ?_
  have key : ∀ z : Z, intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map a.op).hom r) =
      intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map b.op).hom r) := by
    intro z
    have hker : ∀ t : Y.presheaf.obj (op ⊤),
        intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map a.op).hom t) = 0 ↔
          intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map b.op).hom t) = 0 := by
      intro t
      have e1 : intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map a.op).hom t) = 0 ↔
          t ∈ ((a ≫ Y.toLocallyRingedSpace.toΓSpec).base z).asIdeal :=
        ((intrinsicStalkCoefficients Z z).evalHom_eq_zero_iff).trans
          (mem_comp_toΓSpec_base_asIdeal a z t).symm
      have e2 : intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map b.op).hom t) = 0 ↔
          t ∈ ((b ≫ Y.toLocallyRingedSpace.toΓSpec).base z).asIdeal :=
        ((intrinsicStalkCoefficients Z z).evalHom_eq_zero_iff).trans
          (mem_comp_toΓSpec_base_asIdeal b z t).symm
      have hp : (a ≫ Y.toLocallyRingedSpace.toΓSpec).base z =
          (b ≫ Y.toLocallyRingedSpace.toΓSpec).base z := by
        change Y.toLocallyRingedSpace.toΓSpec.base (a.base z) =
          Y.toLocallyRingedSpace.toΓSpec.base (b.base z)
        rw [hab z]
      rw [e1, e2, hp]
    have h1 : intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map a.op).hom
        (r - κ (intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map a.op).hom r)))) = 0 := by
      rw [map_sub, map_sub, hκa, intrinsicEval_const, sub_self]
    have h2 := (hker _).1 h1
    rw [map_sub, map_sub, hκb, intrinsicEval_const, sub_eq_zero] at h2
    exact h2.symm
  have h0 := hZ ((LocallyRingedSpace.Γ.map a.op).hom r - (LocallyRingedSpace.Γ.map b.op).hom r)
    (fun z => by rw [map_sub, key z, sub_self])
  exact sub_eq_zero.1 h0

/-- The actual `ℂ`-constants of `X`, read through its structure map to `Spec ℂ`. -/
def schemeConstant (X : SchemeLFTℂ.{0}) (c : ℂ) : X.obj.left.presheaf.obj (op ⊤) :=
  (LocallyRingedSpace.Γ.map X.obj.hom.toLRSHom.op).hom
    ((ΓSpec.locallyRingedSpaceAdjunction.counit.app
      (op (CommRingCat.of (ULift.{0} ℂ)))).unop.hom (ULift.up c))

/-- The comparison map of an analytic morphism pulls the scheme constants back to the
actual constants of the source. -/
theorem comparison_schemeConstant {Z : AnalyticSpace.{0}} {X : SchemeLFTℂ.{0}}
    (f : Z ⟶ analytification.obj X) (c : ℂ) :
    (LocallyRingedSpace.Γ.map (f.toLRSHom ≫ (analytificationπ X).left).op).hom
      (schemeConstant X c) = Z.algebraMap c := by
  have hcomp : (LocallyRingedSpace.Γ.map (f.toLRSHom ≫ (analytificationπ X).left).op).hom
      (schemeConstant X c) =
      (LocallyRingedSpace.Γ.map
        ((f.toLRSHom ≫ (analytificationπ X).left) ≫ X.obj.hom.toLRSHom).op).hom
        ((ΓSpec.locallyRingedSpaceAdjunction.counit.app
          (op (CommRingCat.of (ULift.{0} ℂ)))).unop.hom (ULift.up c)) := by
    rw [op_comp, Functor.map_comp]
    rfl
  rw [hcomp, comparison_over f]
  exact gamma_toSpecOfAlgMap_counit Z.toLocallyRingedSpace (uliftAlgMap Z.algebraMap) (ULift.up c)

/-- **Rigidity, affine target.** Two analytic maps from a source with value-detected global
sections into the analytification of an affine scheme, with the same actual comparison
points, are equal. -/
theorem analytification_hom_ext_of_base_affine {Z : AnalyticSpace.{0}}
    (hZ : GlobalPointwiseReduced Z) {X : SchemeLFTℂ.{0}} [IsAffine X.obj.left]
    (f g : Z ⟶ analytification.obj X)
    (hb : ∀ z : Z, (f.toLRSHom ≫ (analytificationπ X).left).base z =
      (g.toLRSHom ≫ (analytificationπ X).left).base z) : f = g :=
  analytification_hom_ext_of_gamma f g
    (gamma_eq_of_base_eq hZ _ _ (schemeConstant X) (comparison_schemeConstant f)
      (comparison_schemeConstant g) hb)

/-- **Points from values.** For a morphism from an analytic space into an affine scheme, the
point hit by `z` is the point `y` whose prime is exactly the kernel of "pull back, then take
the intrinsic value at `z`". -/
theorem lrs_base_eq_of_values {Z : AnalyticSpace.{0}} {V : Scheme.{0}} [IsAffine V]
    (a : Z.toLocallyRingedSpace ⟶ V.toLocallyRingedSpace) (z : Z) (y : V)
    (hy : ∀ r : V.presheaf.obj (op ⊤), r ∈ (V.toLocallyRingedSpace.toΓSpec.base y).asIdeal ↔
      intrinsicEval Z (U := ⊤) z trivial ((LocallyRingedSpace.Γ.map a.op).hom r) = 0) :
    a.base z = y := by
  have hinj : Function.Injective V.toSpecΓ.base := V.toSpecΓ.isOpenEmbedding.injective
  apply hinj
  change (a ≫ V.toLocallyRingedSpace.toΓSpec).base z = V.toLocallyRingedSpace.toΓSpec.base y
  refine PrimeSpectrum.ext (Ideal.ext fun r => ?_)
  rw [mem_comp_toΓSpec_base_asIdeal, hy]
  exact ((intrinsicStalkCoefficients Z z).evalHom_eq_zero_iff).symm

/-- **Comparison points from values**, for an analytic map into an affine analytification. -/
theorem comparison_base_eq_of_values {Z : AnalyticSpace.{0}} {X : SchemeLFTℂ.{0}}
    [IsAffine X.obj.left] (f : Z ⟶ analytification.obj X) (z : Z) (y : X.obj.left)
    (hy : ∀ r : X.obj.left.presheaf.obj (op ⊤),
      r ∈ (X.obj.left.toLocallyRingedSpace.toΓSpec.base y).asIdeal ↔
        intrinsicEval Z (U := ⊤) z trivial
          ((LocallyRingedSpace.Γ.map (f.toLRSHom ≫ (analytificationπ X).left).op).hom r) = 0) :
    (f.toLRSHom ≫ (analytificationπ X).left).base z = y :=
  lrs_base_eq_of_values _ z y hy

/-- Comparison points of `f' ≫ analytification.map ι` are the `ι`-images of those of `f'`. -/
theorem comparison_comp_map_base {Z : AnalyticSpace.{u}} {X W : SchemeLFTℂ.{u}} (ι : W ⟶ X)
    (f' : Z ⟶ analytification.obj W) (z : Z) :
    ((f' ≫ analytification.map ι).toLRSHom ≫ (analytificationπ X).left).base z =
      ι.hom.left.base ((f'.toLRSHom ≫ (analytificationπ W).left).base z) :=
  congrArg (fun m => m.base z) (comparison_comp_map ι f')

/-! ### Pointwise reducedness -/

/-- At `z`, a section all of whose intrinsic values vanish has zero germ. -/
def PointwiseReducedAt (Z : AnalyticSpace.{0}) (z : Z) : Prop :=
  ∀ (U : Z.Opens) (hz : z ∈ U) (s : Z.presheaf.obj (op U)),
    (∀ (y : Z) (hy : y ∈ U), intrinsicEval Z y hy s = 0) → Z.presheaf.germ U z hz s = 0

/-- Pointwise reducedness at every point. -/
def PointwiseReduced (Z : AnalyticSpace.{0}) : Prop := ∀ z : Z, PointwiseReducedAt Z z

theorem PointwiseReduced.global {Z : AnalyticSpace.{0}} (h : PointwiseReduced Z) :
    GlobalPointwiseReduced Z := by
  intro s hs
  refine TopCat.Presheaf.section_ext Z.sheaf ⊤ s 0 (fun z hz => ?_)
  rw [map_zero]
  exact h z ⊤ hz s (fun y hy => hs y)

/-- Transport along an analytic morphism injective on the stalk at `z'`. -/
theorem pointwiseReducedAt_of_stalkMap_injective {Z' Z : AnalyticSpace.{0}} (g : Z' ⟶ Z)
    (z' : Z') (hinj : Function.Injective (g.toLRSHom.stalkMap z').hom)
    (h : PointwiseReducedAt Z' z') : PointwiseReducedAt Z (g.toLRSHom.base z') := by
  intro U hz s hs
  apply hinj
  rw [map_zero, LocallyRingedSpace.stalkMap_germ_apply]
  exact h ((Opens.map g.toLRSHom.base).obj U) hz (g.toLRSHom.c.app (op U) s)
    (fun y hy => (intrinsicEval_c_app g.toLRSHom g.isCLinear y hy s).trans (hs _ hy))

/-- Intrinsic stalk values on an open subspace are the ambient ones. -/
theorem intrinsicStalkEval_restrict (Z : AnalyticSpace.{0}) (O : Z.Opens) (w : Z.restrict O)
    (a : (Z.restrict O).presheaf.stalk w) :
    intrinsicStalkEval Z w.1 ((Z.toLocallyRingedSpace.restrictStalkIso O.isOpenEmbedding w).hom a) =
      intrinsicStalkEval (Z.restrict O) w a :=
  (intrinsicStalkCoefficients (Z.restrict O) w).evalHom_map
    (f := (Z.toLocallyRingedSpace.restrictStalkIso O.isOpenEmbedding w).hom.hom)
    (ConcreteCategory.bijective_of_isIso _).surjective
    (fun c => LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap _ _ _ w c) a

/-- Intrinsic section values on an open subspace are the ambient ones. -/
theorem intrinsicEval_restrict (Z : AnalyticSpace.{0}) (O : Z.Opens) (U : (Z.restrict O).Opens)
    (v : Z.restrict O) (hv : v ∈ U) (s : (Z.restrict O).presheaf.obj (op U)) :
    intrinsicEval Z (U := O.isOpenEmbedding.functor.obj U) v.1 ⟨v, hv, rfl⟩ s =
      intrinsicEval (Z.restrict O) v hv s := by
  change intrinsicStalkEval Z v.1 (Z.presheaf.germ _ v.1 _ s) =
    intrinsicStalkEval (Z.restrict O) v ((Z.restrict O).presheaf.germ U v hv s)
  rw [← intrinsicStalkEval_restrict]
  exact congrArg (intrinsicStalkEval Z v.1)
    (LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply Z.toLocallyRingedSpace
      O.isOpenEmbedding U v hv s).symm

/-- Pointwise reducedness is inherited by open subspaces. -/
theorem pointwiseReducedAt_restrict {Z : AnalyticSpace.{0}} (O : Z.Opens) (w : Z.restrict O)
    (h : PointwiseReducedAt Z w.1) : PointwiseReducedAt (Z.restrict O) w := by
  intro U hw s hs
  apply (ConcreteCategory.bijective_of_isIso
    (Z.toLocallyRingedSpace.restrictStalkIso O.isOpenEmbedding w).hom).injective
  rw [map_zero]
  refine (LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply Z.toLocallyRingedSpace
    O.isOpenEmbedding U w hw s).trans ?_
  refine h (O.isOpenEmbedding.functor.obj U) ⟨w, hw, rfl⟩ s ?_
  rintro y ⟨v, hv, rfl⟩
  exact (intrinsicEval_restrict Z O U v hv s).trans (hs v hv)

theorem PointwiseReduced.restrict {Z : AnalyticSpace.{0}} (h : PointwiseReduced Z)
    (O : Z.Opens) : PointwiseReduced (Z.restrict O) :=
  fun w => pointwiseReducedAt_restrict O w (h w.1)

/-- Pointwise reducedness is transported backwards along isomorphisms. -/
theorem PointwiseReduced.of_iso {Z Z' : AnalyticSpace.{0}} (e : Z ≅ Z')
    (h : PointwiseReduced Z') : PointwiseReduced Z := by
  intro z
  have hhi : e.hom.toLRSHom ≫ e.inv.toLRSHom = 𝟙 _ :=
    congrArg AnalyticSpace.Hom.toLRSHom e.hom_inv_id
  have hih : e.inv.toLRSHom ≫ e.hom.toLRSHom = 𝟙 _ :=
    congrArg AnalyticSpace.Hom.toLRSHom e.inv_hom_id
  have : IsIso e.inv.toLRSHom := ⟨⟨e.hom.toLRSHom, hih, hhi⟩⟩
  have hz : e.inv.toLRSHom.base (e.hom.toLRSHom.base z) = z := by
    change (e.hom.toLRSHom ≫ e.inv.toLRSHom).base z = z
    rw [hhi]
    rfl
  have : LocallyRingedSpace.IsOpenImmersion e.inv.toLRSHom :=
    LocallyRingedSpace.IsOpenImmersion.of_isIso e.inv.toLRSHom
  have hinj : Function.Injective (e.inv.toLRSHom.stalkMap (e.hom.toLRSHom.base z)).hom :=
    (ConcreteCategory.bijective_of_isIso
      (e.inv.toLRSHom.stalkMap (e.hom.toLRSHom.base z))).injective
  have H := pointwiseReducedAt_of_stalkMap_injective e.inv _ hinj (h _)
  rwa [hz] at H

/-- Pointwise reducedness is local: it holds wherever an open subspace containing the point
has it. -/
theorem pointwiseReducedAt_of_restrict {Z : AnalyticSpace.{0}} (O : Z.Opens) (w : Z.restrict O)
    (h : PointwiseReducedAt (Z.restrict O) w) : PointwiseReducedAt Z w.1 :=
  pointwiseReducedAt_of_stalkMap_injective (Z.ofRestrict O) w
    (ConcreteCategory.bijective_of_isIso ((Z.ofRestrict O).toLRSHom.stalkMap w)).injective h

/-- **The genuine Euclidean opens are pointwise reduced**: their sections are literal
holomorphic functions, whose intrinsic values are their actual values. -/
theorem euclideanOpen_pointwiseReduced (n : ℕ) (V : Opens (_root_.complexAffineSpace.{0} n)) :
    PointwiseReduced (euclideanOpen n V) := by
  intro z U hz s hs
  have h0 : s = 0 := by
    apply OkaRing.ext
    funext y
    obtain ⟨w, hw, hy⟩ := y.2
    have h1 := (intrinsicEval_open n V w U hw s).symm.trans (hs w hw)
    have hyw : y = ⟨w.1, openOkaMemSectionImage V w U hw⟩ := Subtype.ext hy.symm
    rw [hyw]
    exact h1
  rw [h0, map_zero]

/-- Pointwise reducedness is local: it suffices that every point has an open neighbourhood
whose subspace is pointwise reduced (e.g. one isomorphic to a Euclidean open). -/
theorem pointwiseReduced_of_local {Z : AnalyticSpace.{0}}
    (h : ∀ z : Z, ∃ (O : Z.Opens) (hz : z ∈ O), PointwiseReducedAt (Z.restrict O) ⟨z, hz⟩) :
    PointwiseReduced Z := by
  intro z
  obtain ⟨O, hz, hO⟩ := h z
  exact pointwiseReducedAt_of_restrict O ⟨z, hz⟩ hO

/-! ### Rigidity for arbitrary targets -/

/-- Rigidity through one affine open of the target. -/
theorem analytification_hom_ext_of_base_affineOpen {Z : AnalyticSpace.{0}}
    (hZ : GlobalPointwiseReduced Z) {X : SchemeLFTℂ.{0}} (V : X.obj.left.Opens)
    (hV : IsAffineOpen V) (f g : Z ⟶ analytification.obj X)
    (hfV : ∀ z : Z, (f.toLRSHom ≫ (analytificationπ X).left).base z ∈ V)
    (hb : ∀ z : Z, (f.toLRSHom ≫ (analytificationπ X).left).base z =
      (g.toLRSHom ≫ (analytificationπ X).left).base z) : f = g := by
  have : LocallyOfFiniteType X.obj.hom := X.property
  let W : SchemeLFTℂ.{0} :=
    ⟨Over.mk (V.ι ≫ X.obj.hom), (inferInstance : LocallyOfFiniteType (V.ι ≫ X.obj.hom))⟩
  let ι : W ⟶ X := ObjectProperty.homMk (Over.homMk V.ι rfl)
  have : IsOpenImmersion ι.hom.left := (inferInstance : IsOpenImmersion V.ι)
  have : IsAffine W.obj.left := hV
  have hrange : ∀ h : Z ⟶ analytification.obj X,
      (∀ z : Z, (h.toLRSHom ≫ (analytificationπ X).left).base z ∈ V) →
      Set.range (h.toLRSHom ≫ (analytificationπ X).left).base ⊆ Set.range ι.hom.left.base := by
    intro h hh
    rintro _ ⟨z, rfl⟩
    change _ ∈ Set.range V.ι.base
    rw [Scheme.Opens.range_ι]
    exact hh z
  obtain ⟨f', hf'⟩ := exists_lift_analytification_of_range ι f (hrange f hfV)
  obtain ⟨g', hg'⟩ := exists_lift_analytification_of_range ι g
    (hrange g (fun z => (hb z) ▸ hfV z))
  have hcf := comparison_comp_map ι f'
  have hcg := comparison_comp_map ι g'
  rw [hf'] at hcf
  rw [hg'] at hcg
  have hb' : ∀ z : Z, (f'.toLRSHom ≫ (analytificationπ W).left).base z =
      (g'.toLRSHom ≫ (analytificationπ W).left).base z := by
    intro z
    apply ι.hom.left.isOpenEmbedding.injective
    have e1 := congrArg (fun m => m.base z) hcf
    have e2 := congrArg (fun m => m.base z) hcg
    exact e1.symm.trans ((hb z).trans e2)
  rw [← hf', ← hg', analytification_hom_ext_of_base_affine hZ f' g' hb']

/-- **Rigidity.** Two analytic maps from a pointwise-reduced source into the analytification
of any scheme locally of finite type over `ℂ`, with the same actual comparison points, are
equal. -/
theorem analytification_hom_ext_of_base {Z : AnalyticSpace.{0}} (hZ : PointwiseReduced Z)
    {X : SchemeLFTℂ.{0}} (f g : Z ⟶ analytification.obj X)
    (hb : ∀ z : Z, (f.toLRSHom ≫ (analytificationπ X).left).base z =
      (g.toLRSHom ≫ (analytificationπ X).left).base z) : f = g := by
  let U : X.obj.left.affineOpens → Z.Opens := fun V =>
    (Opens.map (f.toLRSHom ≫ (analytificationπ X).left).base).obj V.1
  have hU : ∀ z : Z, ∃ V, z ∈ U V := by
    intro z
    obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := (f.toLRSHom ≫ (analytificationπ X).left).base z) (U := ⊤) trivial
    exact ⟨⟨W, hW⟩, hzW⟩
  refine AnalyticSpace.hom_ext_of_opens U hU (fun V => ?_)
  exact analytification_hom_ext_of_base_affineOpen ((hZ.restrict (U V)).global) V.1 V.2 _ _
    (fun x => x.2) (fun x => hb x.1)

/-! ### Gluing along actual source charts -/

variable {X : AnalyticSpace.{0}} {Y : SchemeLFTℂ.{0}} {ι : Type}
  (M : ι → X.Opens) (hM : ∀ x : X, ∃ i, x ∈ M i) (Z : ι → AnalyticSpace.{0})
  (e : ∀ i, X.restrict (M i) ≅ Z i) (hZ : ∀ i, PointwiseReduced (Z i))
  (β : ∀ i, Z i ⟶ analytification.obj Y) (P : X → Y.obj.left)

include hM e hZ in
/-- A space covered by opens isomorphic to pointwise-reduced spaces is pointwise reduced. -/
theorem pointwiseReduced_of_charts : PointwiseReduced X := by
  intro x
  obtain ⟨i, hi⟩ := hM x
  exact pointwiseReducedAt_of_restrict (M i) ⟨x, hi⟩ ((hZ i).of_iso (e i) ⟨x, hi⟩)

include hM e hZ in
/-- **Overlap agreement** for chart maps realising one point map `P`. -/
theorem chart_overlap
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((β i).toLRSHom ≫ (analytificationπ Y).left).base ((e i).hom.toLRSHom.base ⟨x, hx⟩) = P x)
    (i j : ι) :
    X.restrictLE (inf_le_left : M i ⊓ M j ≤ M i) ≫ (e i).hom ≫ β i =
      X.restrictLE (inf_le_right : M i ⊓ M j ≤ M j) ≫ (e j).hom ≫ β j := by
  have hl : ∀ {V W : X.Opens} (h : V ≤ W) (y : X.restrict V),
      (X.restrictLE h).toLRSHom.base y = ⟨y.1, h y.2⟩ := fun h y =>
    Subtype.ext (congrArg (fun m => m.base y)
      (LocallyRingedSpace.restrictLE_fac X.toLocallyRingedSpace h))
  refine analytification_hom_ext_of_base
    ((pointwiseReduced_of_charts M hM Z e hZ).restrict (M i ⊓ M j)) _ _ (fun y => ?_)
  change ((β i).toLRSHom ≫ (analytificationπ Y).left).base
      ((e i).hom.toLRSHom.base ((X.restrictLE (inf_le_left : M i ⊓ M j ≤ M i)).toLRSHom.base y)) =
    ((β j).toLRSHom ≫ (analytificationπ Y).left).base
      ((e j).hom.toLRSHom.base ((X.restrictLE (inf_le_right : M i ⊓ M j ≤ M j)).toLRSHom.base y))
  rw [hl, hl]
  exact (hP i y.1 y.2.1).trans (hP j y.1 y.2.2).symm

/-- **The glued analytic map** `X ⟶ Y^an`, built by the actual `glueMorphismsOfOpens` from the
chart maps `(e i).hom ≫ β i`. -/
def chartGlue
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((β i).toLRSHom ≫ (analytificationπ Y).left).base ((e i).hom.toLRSHom.base ⟨x, hx⟩) = P x) :
    X ⟶ analytification.obj Y :=
  AnalyticSpace.glueMorphismsOfOpens M hM (fun i => (e i).hom ≫ β i)
    (chart_overlap M hM Z e hZ β P hP)

/-- The glued map restricts on each chart to the given chart map. -/
theorem ofRestrict_comp_chartGlue
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((β i).toLRSHom ≫ (analytificationπ Y).left).base ((e i).hom.toLRSHom.base ⟨x, hx⟩) = P x)
    (i : ι) : X.ofRestrict (M i) ≫ chartGlue M hM Z e hZ β P hP = (e i).hom ≫ β i :=
  AnalyticSpace.ofRestrict_comp_glueMorphismsOfOpens M hM _ _ i

/-- **Original point realisation**: the actual comparison map of the glued map is `P`. -/
theorem chartGlue_base
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((β i).toLRSHom ≫ (analytificationπ Y).left).base ((e i).hom.toLRSHom.base ⟨x, hx⟩) = P x)
    (x : X) :
    ((chartGlue M hM Z e hZ β P hP).toLRSHom ≫ (analytificationπ Y).left).base x = P x := by
  obtain ⟨i, hi⟩ := hM x
  have h := congrArg (fun m : X.restrict (M i) ⟶ analytification.obj Y =>
    (m.toLRSHom ≫ (analytificationπ Y).left).base ⟨x, hi⟩)
    (ofRestrict_comp_chartGlue M hM Z e hZ β P hP i)
  exact h.trans (hP i x hi)

/-- **Uniqueness**: any analytic map `X ⟶ Y^an` restricting to the chart maps is the glued map. -/
theorem chartGlue_unique
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((β i).toLRSHom ≫ (analytificationπ Y).left).base ((e i).hom.toLRSHom.base ⟨x, hx⟩) = P x)
    (ψ : X ⟶ analytification.obj Y) (hψ : ∀ i, X.ofRestrict (M i) ≫ ψ = (e i).hom ≫ β i) :
    ψ = chartGlue M hM Z e hZ β P hP :=
  AnalyticSpace.hom_ext_of_opens M hM
    (fun i => (hψ i).trans (ofRestrict_comp_chartGlue M hM Z e hZ β P hP i).symm)

/-- **Uniqueness from points alone**: any analytic map `X ⟶ Y^an` realising `P` is the glued
map (rigidity on the pointwise-reduced source). -/
theorem chartGlue_unique_of_base
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((β i).toLRSHom ≫ (analytificationπ Y).left).base ((e i).hom.toLRSHom.base ⟨x, hx⟩) = P x)
    (ψ : X ⟶ analytification.obj Y)
    (hψ : ∀ x : X, (ψ.toLRSHom ≫ (analytificationπ Y).left).base x = P x) :
    ψ = chartGlue M hM Z e hZ β P hP :=
  analytification_hom_ext_of_base (pointwiseReduced_of_charts M hM Z e hZ) _ _
    (fun x => (hψ x).trans (chartGlue_base M hM Z e hZ β P hP x).symm)

/-! ### Gluing local maps out of a pointwise-reduced source (no chart isomorphism needed) -/

section ReducedGlue

variable {X : AnalyticSpace.{0}} {Y : SchemeLFTℂ.{0}} {ι : Type}
  (M : ι → X.Opens) (hM : ∀ x : X, ∃ i, x ∈ M i) (hX : PointwiseReduced X)
  (φ : ∀ i, X.restrict (M i) ⟶ analytification.obj Y) (P : X → Y.obj.left)

include hX in
/-- **Overlap agreement** for local maps out of a pointwise-reduced space realising one point
map `P`. -/
theorem reduced_overlap
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((φ i).toLRSHom ≫ (analytificationπ Y).left).base ⟨x, hx⟩ = P x)
    (i j : ι) :
    X.restrictLE (inf_le_left : M i ⊓ M j ≤ M i) ≫ φ i =
      X.restrictLE (inf_le_right : M i ⊓ M j ≤ M j) ≫ φ j := by
  have hl : ∀ {V W : X.Opens} (h : V ≤ W) (y : X.restrict V),
      (X.restrictLE h).toLRSHom.base y = ⟨y.1, h y.2⟩ := fun h y =>
    Subtype.ext (congrArg (fun m => m.base y)
      (LocallyRingedSpace.restrictLE_fac X.toLocallyRingedSpace h))
  refine analytification_hom_ext_of_base (hX.restrict (M i ⊓ M j)) _ _ (fun y => ?_)
  change ((φ i).toLRSHom ≫ (analytificationπ Y).left).base
      ((X.restrictLE (inf_le_left : M i ⊓ M j ≤ M i)).toLRSHom.base y) =
    ((φ j).toLRSHom ≫ (analytificationπ Y).left).base
      ((X.restrictLE (inf_le_right : M i ⊓ M j ≤ M j)).toLRSHom.base y)
  rw [hl, hl]
  exact (hP i y.1 y.2.1).trans (hP j y.1 y.2.2).symm

/-- **The glued analytic map** out of a pointwise-reduced space, by the actual
`glueMorphismsOfOpens`. -/
def reducedGlue
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((φ i).toLRSHom ≫ (analytificationπ Y).left).base ⟨x, hx⟩ = P x) :
    X ⟶ analytification.obj Y :=
  AnalyticSpace.glueMorphismsOfOpens M hM φ (reduced_overlap M hX φ P hP)

theorem ofRestrict_comp_reducedGlue
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((φ i).toLRSHom ≫ (analytificationπ Y).left).base ⟨x, hx⟩ = P x) (i : ι) :
    X.ofRestrict (M i) ≫ reducedGlue M hM hX φ P hP = φ i :=
  AnalyticSpace.ofRestrict_comp_glueMorphismsOfOpens M hM _ _ i

/-- **Point realisation**: the comparison map of the glued map is `P`. -/
theorem reducedGlue_base
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((φ i).toLRSHom ≫ (analytificationπ Y).left).base ⟨x, hx⟩ = P x) (x : X) :
    ((reducedGlue M hM hX φ P hP).toLRSHom ≫ (analytificationπ Y).left).base x = P x := by
  obtain ⟨i, hi⟩ := hM x
  have h := congrArg (fun m : X.restrict (M i) ⟶ analytification.obj Y =>
    (m.toLRSHom ≫ (analytificationπ Y).left).base ⟨x, hi⟩)
    (ofRestrict_comp_reducedGlue M hM hX φ P hP i)
  exact h.trans (hP i x hi)

/-- **Uniqueness from points alone.** -/
theorem reducedGlue_unique_of_base
    (hP : ∀ i (x : X) (hx : x ∈ M i),
      ((φ i).toLRSHom ≫ (analytificationπ Y).left).base ⟨x, hx⟩ = P x)
    (ψ : X ⟶ analytification.obj Y)
    (hψ : ∀ x : X, (ψ.toLRSHom ≫ (analytificationπ Y).left).base x = P x) :
    ψ = reducedGlue M hM hX φ P hP :=
  analytification_hom_ext_of_base hX _ _
    (fun x => (hψ x).trans (reducedGlue_base M hM hX φ P hP x).symm)

end ReducedGlue

end ZInQ.Contrib.CloudB3W17bNativeGlue
