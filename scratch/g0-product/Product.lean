import Mathlib

/-!
# g0-product: the glue piece `ProductExists` (G17)

Check with `lake env lean scratch/g0-product/Product.lean`.

§1 copies, verbatim from `scratch/g0-split/Split.lean`, the definitions the piece depends on:
`PkgI3.AbVar` with `PkgI3.AbVar.dim` (Split.lean l. 2524-2543), `ZInQ.DefFaltings.AbVar` with
`ZInQ.DefFaltings.AbVar.dim` (l. 17798-17820), `G0Split.IsProductOf` (l. 19463) and
`G0Split.ProductExists` (l. 19570).

§2 proves, from Mathlib alone, that the fibre product `A ×_L Z` (Mathlib's cartesian monoidal
product `A.X ⊗ Z.X` in `Over (Spec L)`, whose underlying scheme is `pullback A.X.hom Z.X.hom`)
is a group scheme over `L` that is proper, smooth and geometrically integral, i.e. a
`ZInQ.DefFaltings.AbVar L`, and that `IsProductOf (A.X ⊗ Z.X) A.X Z.X` holds with the two
projections.

§3 proves `ProductExists` from one strictly smaller named Prop, `DimProductOverField`
(dimension of a product of schemes of finite type over a field, a textbook theorem).
-/

noncomputable section

/-! ## §1. Verbatim copies -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

end AbVar

end PkgI3

namespace ZInQ.DefFaltings

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group
object in schemes over `Spec K`, proper, smooth and geometrically integral. -/
structure AbVar (K : Type) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) The dimension of `A` (Krull dimension of the
underlying space). -/
noncomputable def AbVar.dim {K : Type} [Field K] (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

end ModelsSec

end ZInQ.DefFaltings

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.DefFaltings

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)

/-- **Missing piece 7 (definition-level glue; G17).** The product `A × Z` of abelian varieties is an
abelian variety `P` (proper, smooth, geometrically integral group scheme), with
`dim P = dim A + dim Z` (Mumford §4; STANDARD; geometric integrality of products is not in
Mathlib). -/
def ProductExists : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A Z : PkgI3.AbVar L),
    ∃ P : ZInQ.DefFaltings.AbVar L, IsProductOf P.X A.X Z.X ∧ P.dim = A.dim + Z.dim

end G0Split

/-! ## §2. The product is an abelian variety (proved, Mathlib only) -/

namespace G0Product

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Glue (proved).** Geometric integrality is stable under composition `X → Y → S` when the
first map is geometrically integral, flat and universally open and the second is geometrically
integral and locally of finite type. For a field `K` and `Spec K → S`, the base change
`X ×_S K = X ×_Y (Y ×_S K)` is integral by Mathlib's
`AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` applied over the
integral, locally noetherian scheme `Y ×_S K`. -/
theorem geometricallyIntegral_comp {X Y S : Scheme} (g : X ⟶ Y) (h : Y ⟶ S)
    [GeometricallyIntegral g] [Flat g] [UniversallyOpen g]
    [GeometricallyIntegral h] [LocallyOfFiniteType h] :
    GeometricallyIntegral (g ≫ h) := by
  refine ⟨fun K _ y Z fst snd hP => ?_⟩
  have : IsIntegral (pullback h y) := pullback_of_geometrically
    (GeometricallyIntegral.geometrically_isIntegral (f := h)) K y
  have : IsLocallyNoetherian (pullback h y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h y)
  have hI : IsIntegral (pullback g (pullback.fst h y)) := inferInstance
  let e : Z ≅ pullback g (pullback.fst h y) :=
    hP.isoPullback ≪≫ (pullbackRightPullbackFstIso h y g).symm
  have : Nonempty Z := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- **Glue (proved).** The fibre product `A ×_K Z` of two abelian varieties over a field `K`
(Mathlib's cartesian monoidal product `A.X ⊗ Z.X` in `Over (Spec K)`, with the product group
structure `GrpObj.tensorObj.instTensorObj`) is an abelian variety in the sense of
`ZInQ.DefFaltings.AbVar`: proper and smooth (composition and base change) and geometrically
integral (`geometricallyIntegral_comp`). -/
def prodAbVar {K : Type} [Field K] (A Z : PkgI3.AbVar K) : ZInQ.DefFaltings.AbVar K :=
  haveI : IsProper (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : Smooth (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (A.X ⊗ Z.X).hom := by
    rw [Over.tensorObj_hom]; exact geometricallyIntegral_comp _ _
  { X := A.X ⊗ Z.X }

@[simp] lemma prodAbVar_X {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    (prodAbVar A Z).X = A.X ⊗ Z.X := rfl

/-- **Glue (proved).** `prodAbVar A Z` is the product of `A` and `Z` in the sense of
`G0Split.IsProductOf`, via the two projections (homomorphisms for the product group law;
`(fst, snd) = 𝟙`). -/
theorem isProductOf_prodAbVar {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    G0Split.IsProductOf (prodAbVar A Z).X A.X Z.X := by
  change G0Split.IsProductOf (A.X ⊗ Z.X) A.X Z.X
  exact ⟨fst A.X Z.X, snd A.X Z.X, inferInstance, inferInstance, by
    rw [lift_fst_snd]; infer_instance⟩

/-- The dimension of `prodAbVar A Z` is the Krull dimension of the fibre product scheme. -/
lemma prodAbVar_dim {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    (prodAbVar A Z).dim = topologicalKrullDim (pullback (C := Scheme) A.X.hom Z.X.hom) := rfl

end G0Product

/-! ## §3. `ProductExists` from the dimension formula -/

namespace G0Product

open CategoryTheory AlgebraicGeometry Limits

/-- **Textbook leaf (dimension of a product over a field).** For schemes `X`, `Y` of finite
type over a field `K`, `dim (X ×_K Y) = dim X + dim Y` (Krull dimensions of the underlying
spaces, in `WithBot ℕ∞`; both sides are `⊥` if `X` or `Y` is empty). Source: Stacks Project,
Varieties, Lemma 33.20.5 (Tag 0B2L?, UNVERIFIED number); Görtz-Wedhorn, *Algebraic Geometry I*,
Prop. 5.37 (UNVERIFIED number); for integral `X`, `Y` over an algebraically closed field,
Hartshorne II Ex. 3.20 / I Prop. 1.10 style transcendence-degree argument. STANDARD. -/
def DimProductOverField : Prop :=
  ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K))
    (g : Y ⟶ Spec (CommRingCat.of K)), LocallyOfFiniteType f → QuasiCompact f →
    LocallyOfFiniteType g → QuasiCompact g →
    topologicalKrullDim (pullback (C := Scheme) f g) = topologicalKrullDim X + topologicalKrullDim Y

/-- **G17, `ProductExists`, proved from `DimProductOverField`.** -/
theorem productExists_of_dimProduct (hD : DimProductOverField) : G0Split.ProductExists := by
  intro L _ _ A Z
  refine ⟨prodAbVar A Z, isProductOf_prodAbVar A Z, ?_⟩
  rw [prodAbVar_dim]
  exact hD L A.X.left Z.X.left A.X.hom Z.X.hom inferInstance inferInstance inferInstance
    inferInstance

end G0Product

#print axioms G0Product.productExists_of_dimProduct
