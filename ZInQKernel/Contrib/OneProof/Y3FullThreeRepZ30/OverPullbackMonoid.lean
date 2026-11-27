import Mathlib

/-!
# The pullback adjunction on over categories is multiplicative on hom-sets

Let `C` be a category with pullbacks, `f : X ⟶ Y` a morphism, `M : Over Y` a monoid object
for the cartesian monoidal structure on `Over Y` (given by pullbacks), and `A : Over X`.
Mathlib provides the adjunction `Over.mapPullbackAdj f : Over.map f ⊣ Over.pullback f` and
a braided (hence monoidal) structure on `Over.pullback f`, so `(Over.pullback f).obj M` is
again a monoid object. Hom-sets into monoid objects carry the convolution monoid structure
`Hom.monoid`.

We show that the adjunction bijection
`((Over.map f).obj A ⟶ M) ≃ (A ⟶ (Over.pullback f).obj M)`
is a monoid isomorphism, and specialise to points: for `s : W ⟶ Y`, morphisms
`Over.mk s ⟶ M` correspond multiplicatively to sections `𝟙_ (Over W) ⟶ (Over.pullback s).obj M`.

## Main statements

* `map_mul_hom`, `map_one_hom`: a monoidal functor between cartesian monoidal categories is
  multiplicative on hom-sets into a monoid object. These restate `Functor.map_mul` and
  `Functor.map_one` from Mathlib. `map_mul_hom_eq_lift` spells out the structure maps.
* `comp_mul`, `comp_one`: precomposition is multiplicative. These restate `MonObj.comp_mul`
  and `MonObj.comp_one` from Mathlib.
* `homEquiv_mul`, `homEquiv_one`, `homEquiv_pow`, `homMulEquiv`: the adjunction bijection
  is a monoid isomorphism.
* `mapUnitIso`, `pointMulEquiv`, `pointMulEquiv_pow`: the specialisation to points.

All results are stated for monoid objects; a group object `[GrpObj M]` is in particular a
monoid object, see the examples at the end of the file.
-/

noncomputable section

namespace Y3OverPullbackMonoid

open CategoryTheory CategoryTheory.MonoidalCategory

/- The convolution monoid on hom-sets, the monoid object structure on the image of a monoid
object under a lax monoidal functor, and the cartesian monoidal and braided structures on
over categories are not global instances in Mathlib, so we activate them locally. -/
attribute [local instance] CategoryTheory.Hom.monoid CategoryTheory.Functor.monObjObj
  CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Over.braidedCategory

section General

variable {D : Type*} [Category D] [CartesianMonoidalCategory D]
  {E : Type*} [Category E] [CartesianMonoidalCategory E]

/-- A monoidal functor is multiplicative on morphisms into a monoid object, where `G.obj M`
carries the induced monoid object structure. This is `Functor.map_mul` in Mathlib. -/
theorem map_mul_hom (G : D ⥤ E) [G.Monoidal] {T M : D} [MonObj M] (u v : T ⟶ M) :
    G.map (u * v) = G.map u * G.map v :=
  G.map_mul u v

/-- A monoidal functor sends the unit of `T ⟶ M` to the unit of `G.obj T ⟶ G.obj M`.
This is `Functor.map_one` in Mathlib. -/
theorem map_one_hom (G : D ⥤ E) [G.Monoidal] {T M : D} [MonObj M] :
    G.map (1 : T ⟶ M) = 1 :=
  G.map_one

/-- The same statement with the structure maps made explicit: the product of `G.map u` and
`G.map v` is computed with the lax structure map `μ G M M` followed by `G.map` of the
multiplication of `M`. -/
theorem map_mul_hom_eq_lift (G : D ⥤ E) [G.Monoidal] {T M : D} [MonObj M] (u v : T ⟶ M) :
    G.map (u * v) =
      CartesianMonoidalCategory.lift (G.map u) (G.map v) ≫
        Functor.LaxMonoidal.μ G M M ≫ G.map MonObj.mul := by
  rw [G.map_mul, Hom.mul_def, Functor.obj.μ_def]

/-- Precomposition is multiplicative. This is `MonObj.comp_mul` in Mathlib. -/
theorem comp_mul {T T' M : D} [MonObj M] (h : T' ⟶ T) (u v : T ⟶ M) :
    h ≫ (u * v) = (h ≫ u) * (h ≫ v) :=
  MonObj.comp_mul h u v

/-- Precomposition preserves the unit. This is `MonObj.comp_one` in Mathlib. -/
theorem comp_one {T T' M : D} [MonObj M] (h : T' ⟶ T) :
    h ≫ (1 : T ⟶ M) = 1 :=
  MonObj.comp_one h

/-- Precomposition with an isomorphism, as a monoid isomorphism of hom-sets into a monoid
object. -/
def precompMulEquiv {P Q N : D} [MonObj N] (e : P ≅ Q) : (Q ⟶ N) ≃* (P ⟶ N) where
  toFun u := e.hom ≫ u
  invFun u := e.inv ≫ u
  left_inv u := by simp
  right_inv u := by simp
  map_mul' u v := MonObj.comp_mul e.hom u v

theorem precompMulEquiv_apply {P Q N : D} [MonObj N] (e : P ≅ Q) (u : Q ⟶ N) :
    precompMulEquiv e u = e.hom ≫ u :=
  rfl

end General

section Main

variable {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C} (f : X ⟶ Y)
  (A : Over X) (M : Over Y) [MonObj M]

/-- The adjunction bijection is the unit followed by `Over.pullback f`. -/
theorem homEquiv_eq (u : (Over.map f).obj A ⟶ M) :
    (Over.mapPullbackAdj f).homEquiv A M u =
      (Over.mapPullbackAdj f).unit.app A ≫ (Over.pullback f).map u :=
  (Over.mapPullbackAdj f).homEquiv_unit A M u

/-- The adjunction bijection `Over.map f ⊣ Over.pullback f` is multiplicative. -/
theorem homEquiv_mul (u v : (Over.map f).obj A ⟶ M) :
    (Over.mapPullbackAdj f).homEquiv A M (u * v) =
      (Over.mapPullbackAdj f).homEquiv A M u * (Over.mapPullbackAdj f).homEquiv A M v := by
  rw [homEquiv_eq f A M (u * v), homEquiv_eq f A M u, homEquiv_eq f A M v,
    CategoryTheory.Functor.map_mul, MonObj.comp_mul]

/-- The adjunction bijection `Over.map f ⊣ Over.pullback f` preserves the unit. -/
theorem homEquiv_one :
    (Over.mapPullbackAdj f).homEquiv A M 1 = 1 := by
  rw [homEquiv_eq f A M 1, CategoryTheory.Functor.map_one, MonObj.comp_one]

/-- The adjunction bijection `Over.map f ⊣ Over.pullback f` preserves natural powers. -/
theorem homEquiv_pow (u : (Over.map f).obj A ⟶ M) (n : ℕ) :
    (Over.mapPullbackAdj f).homEquiv A M (u ^ n) =
      ((Over.mapPullbackAdj f).homEquiv A M u) ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using homEquiv_one f A M
  | succ n ih => rw [pow_succ, pow_succ, homEquiv_mul f A M, ih]

/-- The adjunction bijection `Over.map f ⊣ Over.pullback f` as a monoid isomorphism. -/
def homMulEquiv : ((Over.map f).obj A ⟶ M) ≃* (A ⟶ (Over.pullback f).obj M) where
  toEquiv := (Over.mapPullbackAdj f).homEquiv A M
  map_mul' u v := homEquiv_mul f A M u v

theorem homMulEquiv_apply (u : (Over.map f).obj A ⟶ M) :
    homMulEquiv f A M u = (Over.mapPullbackAdj f).homEquiv A M u :=
  rfl

end Main

section Points

variable {C : Type*} [Category C] [Limits.HasPullbacks C] {W Y : C} (s : W ⟶ Y)
  (M : Over Y) [MonObj M]

/-- `Over.map s` sends the terminal object `𝟙_ (Over W)` (whose structure map is `𝟙 W`) to an
object isomorphic to `Over.mk s`. The underlying map is the identity of `W`. -/
def mapUnitIso : (Over.map s).obj (𝟙_ (Over W)) ≅ Over.mk s :=
  Over.isoMk (Iso.refl _) (by simp [Over.map_obj_hom, Over.tensorUnit_hom])

/-- Morphisms `Over.mk s ⟶ M` correspond to sections of the pullback `(Over.pullback s).obj M`
over `W`, as a monoid isomorphism. -/
def pointMulEquiv : (Over.mk s ⟶ M) ≃* (𝟙_ (Over W) ⟶ (Over.pullback s).obj M) :=
  (precompMulEquiv (mapUnitIso s)).trans (homMulEquiv s (𝟙_ (Over W)) M)

theorem pointMulEquiv_apply (u : Over.mk s ⟶ M) :
    pointMulEquiv s M u =
      (Over.mapPullbackAdj s).homEquiv (𝟙_ (Over W)) M ((mapUnitIso s).hom ≫ u) :=
  rfl

theorem pointMulEquiv_mul (u v : Over.mk s ⟶ M) :
    pointMulEquiv s M (u * v) = pointMulEquiv s M u * pointMulEquiv s M v :=
  map_mul (pointMulEquiv s M) u v

theorem pointMulEquiv_one :
    pointMulEquiv s M 1 = 1 :=
  map_one (pointMulEquiv s M)

theorem pointMulEquiv_pow (u : Over.mk s ⟶ M) (n : ℕ) :
    pointMulEquiv s M (u ^ n) = pointMulEquiv s M u ^ n :=
  map_pow (pointMulEquiv s M) u n

end Points

section GroupObjects

/-! The results apply verbatim to group objects, through `GrpObj.toMonObj`. -/

example {C : Type*} [Category C] [Limits.HasPullbacks C] {X Y : C} (f : X ⟶ Y)
    (A : Over X) (M : Over Y) [GrpObj M] (u : (Over.map f).obj A ⟶ M) (n : ℕ) :
    (Over.mapPullbackAdj f).homEquiv A M (u ^ n) =
      ((Over.mapPullbackAdj f).homEquiv A M u) ^ n :=
  homEquiv_pow f A M u n

example {C : Type*} [Category C] [Limits.HasPullbacks C] {W Y : C} (s : W ⟶ Y)
    (M : Over Y) [GrpObj M] (u : Over.mk s ⟶ M) (n : ℕ) :
    pointMulEquiv s M (u ^ n) = pointMulEquiv s M u ^ n :=
  pointMulEquiv_pow s M u n

/-- The case of schemes. -/
example {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) (A : Over X) (M : Over Y)
    [GrpObj M] (u v : (Over.map f).obj A ⟶ M) :
    (Over.mapPullbackAdj f).homEquiv A M (u * v) =
      (Over.mapPullbackAdj f).homEquiv A M u * (Over.mapPullbackAdj f).homEquiv A M v :=
  homEquiv_mul f A M u v

end GroupObjects

end Y3OverPullbackMonoid
