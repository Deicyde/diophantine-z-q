import ZInQKernel.Contrib.OneProof.ColmezProperModel.Valuative
import ZInQKernel.Contrib.G9.I4Layer

/-!
# Points of a proper model over a valuation ring

Let `O` be a ring, `F` an `O`-algebra which is a field, and `A` an abelian variety over `F` in the
tree's form (`ZInQ.Contrib.G9.PkgI4.I3.AbVar F`). A *model* of `A` over `O` is here a scheme
`𝒳` with `π : 𝒳 ⟶ Spec O` and an isomorphism of `F`-schemes `e` from the generic fibre
`𝒳 ×_{Spec O} Spec F` to `A`.

* `genericEquiv`: for a field `L` over `F`, the `L`-points of `𝒳` over `Spec O` are the
  `L`-points `A.Pt L` of `A` (universal property of the fibre product, then `e`);
  `genericEquiv_gal`: this is equivariant for `Aut_F(L)`, acting on `A.Pt L` by `A.galAct`.
* `modelEquiv`: if moreover `π` is proper, `R` is a valuation ring with fraction field `K`, `K` is
  an `F`-algebra, and `ι : O →+* R` is compatible with `O → F → K`, then
  `{x : Spec R ⟶ 𝒳 | x ≫ π = Spec ι} ≃ A.Pt K` (valuative criterion, `Valuative.lean`).
* `modelEquiv_act`: a ring endomorphism `τ` of `R` fixing `ι` and extending to `τK ∈ Aut_F(K)`
  acts on the left by `x ↦ Spec τ ≫ x` and on the right by `A.galAct τK`; `modelEquiv`
  intertwines the two actions.
-/

open CategoryTheory AlgebraicGeometry Limits
open ZInQ.Contrib.G9.PkgI4

set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.ColmezProperModel

universe u

section GenericFibre

variable {O F L : Type u} [CommRing O] [Field F] [Algebra O F] [Field L] [Algebra F L]
  {𝒳 : Scheme.{u}} (π : 𝒳 ⟶ Spec (CommRingCat.of O)) (A : I3.AbVar F)
  (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap O F))) ≅ A.X.left)
  (he : e.hom ≫ A.X.hom = pullback.snd _ _)

variable (O F L) in
/-- `Spec L ⟶ Spec O` through `O → F → L`. -/
abbrev specOver : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom ((algebraMap F L).comp (algebraMap O F)))

variable (O F L) in
theorem specOver_eq : Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap O F)) = specOver O F L := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable (F L) in
/-- The `L`-points of `𝒳` over `Spec O` (through `O → F → L`). -/
abbrev OverPts : Type u := {z : Spec (CommRingCat.of L) ⟶ 𝒳 // z ≫ π = specOver O F L}

/-- `σ ∈ Aut_F(L)` acting on `L`-points of `𝒳` over `Spec O`: `z ↦ Spec σ ≫ z`. -/
def overGal (σ : L ≃ₐ[F] L) (z : OverPts F L π) : OverPts F L π :=
  ⟨Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ z.1, by
    rw [Category.assoc, z.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp⟩

/-- The morphism `Spec L ⟶ 𝒳 ×_{Spec O} Spec F` of an `L`-point of `𝒳` over `Spec O`. -/
def liftPt (z : OverPts F L π) :
    Spec (CommRingCat.of L) ⟶ pullback π (Spec.map (CommRingCat.ofHom (algebraMap O F))) :=
  pullback.lift z.1 (Spec.map (CommRingCat.ofHom (algebraMap F L))) (by rw [z.2, specOver_eq])

@[simp] theorem liftPt_fst (z : OverPts F L π) : liftPt π z ≫ pullback.fst _ _ = z.1 :=
  pullback.lift_fst _ _ _

@[simp] theorem liftPt_snd (z : OverPts F L π) :
    liftPt π z ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap F L)) :=
  pullback.lift_snd _ _ _

/-- The underlying morphism `Spec L ⟶ A` of an `L`-point of `A`. -/
abbrev ptLeft (P : A.Pt L) : Spec (CommRingCat.of L) ⟶ A.X.left := P.left

theorem ptLeft_w (P : A.Pt L) :
    ptLeft A P ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap F L)) := Over.w P

theorem inv_snd (he : e.hom ≫ A.X.hom = pullback.snd _ _) :
    e.inv ≫ pullback.snd _ _ = A.X.hom := by
  rw [← he, Iso.inv_hom_id_assoc]

/-- An `L`-point of `𝒳` over `Spec O` as an `L`-point of `A`. -/
def toPt (he : e.hom ≫ A.X.hom = pullback.snd _ _) (z : OverPts F L π) : A.Pt L :=
  Over.homMk (liftPt π z ≫ e.hom) (by
    change (liftPt π z ≫ e.hom) ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap F L))
    rw [Category.assoc, he, liftPt_snd])

theorem toPt_left (z : OverPts F L π) : (toPt π A e he z).left = liftPt π z ≫ e.hom := rfl

/-- An `L`-point of `A` as an `L`-point of `𝒳` over `Spec O`. -/
def ofPt (he : e.hom ≫ A.X.hom = pullback.snd _ _) (P : A.Pt L) : OverPts F L π :=
  ⟨ptLeft A P ≫ e.inv ≫ pullback.fst _ _, by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv,
      inv_snd π A e he, ← Category.assoc, ptLeft_w]
    exact specOver_eq O F L⟩

theorem ofPt_coe (P : A.Pt L) : (ofPt π A e he P).1 = ptLeft A P ≫ e.inv ≫ pullback.fst _ _ :=
  rfl

/-- **The generic fibre**: `L`-points of `𝒳` over `Spec O` are the `L`-points of `A`. -/
def genericEquiv (he : e.hom ≫ A.X.hom = pullback.snd _ _) : OverPts F L π ≃ A.Pt L where
  toFun := toPt π A e he
  invFun := ofPt π A e he
  left_inv z := by
    apply Subtype.ext
    rw [ofPt_coe]
    change (liftPt π z ≫ e.hom) ≫ e.inv ≫ pullback.fst _ _ = z.1
    simp
  right_inv P := by
    apply Over.OverMorphism.ext
    rw [toPt_left]
    have h : liftPt π (ofPt π A e he P) = ptLeft A P ≫ e.inv := by
      apply pullback.hom_ext
      · rw [liftPt_fst, ofPt_coe, Category.assoc]
      · rw [liftPt_snd, Category.assoc, inv_snd π A e he, ptLeft_w]
    rw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem genericEquiv_apply (z : OverPts F L π) : genericEquiv π A e he z = toPt π A e he z := rfl

/-- **`G_F`-equivariance on the generic fibre.** -/
theorem genericEquiv_gal (σ : L ≃ₐ[F] L) (z : OverPts F L π) :
    genericEquiv π A e he (overGal π σ z) = A.galAct σ (genericEquiv π A e he z) := by
  apply Over.OverMorphism.ext
  change liftPt π (overGal π σ z) ≫ e.hom =
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ (liftPt π z ≫ e.hom)
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [liftPt_fst, Category.assoc, liftPt_fst]
    rfl
  · rw [liftPt_snd, Category.assoc, liftPt_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp

end GenericFibre

section Model

variable {O F R K : Type u} [CommRing O] [Field F] [Algebra O F] [CommRing R] [IsDomain R]
  [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra F K]
  {𝒳 : Scheme.{u}} (π : 𝒳 ⟶ Spec (CommRingCat.of O)) (A : I3.AbVar F)
  (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap O F))) ≅ A.X.left)
  (he : e.hom ≫ A.X.hom = pullback.snd _ _)
  (ι : O →+* R) (hι : (algebraMap R K).comp ι = (algebraMap F K).comp (algebraMap O F))

variable (R) in
/-- **`𝒳(R)`**: the sections `x : Spec R ⟶ 𝒳` with `x ≫ π = Spec ι`. -/
abbrev ModelPts : Type u :=
  {x : Spec (CommRingCat.of R) ⟶ 𝒳 // x ≫ π = Spec.map (CommRingCat.ofHom ι)}

include hι in
theorem specFrac_specMap_eq : specFrac R K ≫ Spec.map (CommRingCat.ofHom ι) = specOver O F K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hι]

/-- A ring endomorphism `τ` of `R` fixing `ι` acting on `𝒳(R)`: `x ↦ Spec τ ≫ x`. -/
def modelAct (τ : R →+* R) (hτ : τ.comp ι = ι) (x : ModelPts R π ι) : ModelPts R π ι :=
  ⟨Spec.map (CommRingCat.ofHom τ) ≫ x.1, by
    rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]⟩

variable [IsProper π]

include hι in
/-- **`𝒳(R) = A(K)`** for a proper model `𝒳` of `A` over `O` and a valuation ring `R` with
fraction field `K` (valuative criterion, then the generic fibre). -/
def modelEquiv : ModelPts R π ι ≃ A.Pt K :=
  (restrictEquiv π R K (valuativeCriterion_of_isProper π) (Spec.map (CommRingCat.ofHom ι))).trans
    ((Equiv.subtypeEquivRight fun z => by rw [specFrac_specMap_eq ι hι]).trans
      (genericEquiv π A e he))

include hι in
theorem modelEquiv_apply (x : ModelPts R π ι) : modelEquiv π A e he ι hι x =
    toPt π A e he ⟨specFrac R K ≫ x.1, by
      rw [Category.assoc, x.2, specFrac_specMap_eq ι hι]⟩ := rfl

/-- **Equivariance**: if `τ` fixes `ι` and extends to `τK ∈ Aut_F(K)`, then `modelEquiv` sends
`Spec τ ≫ x` to `A.galAct τK (modelEquiv x)`. -/
theorem modelEquiv_act (τ : R →+* R) (hτ : τ.comp ι = ι) (τK : K ≃ₐ[F] K)
    (hτK : ∀ r, algebraMap R K (τ r) = τK (algebraMap R K r)) (x : ModelPts R π ι) :
    modelEquiv π A e he ι hι (modelAct π ι τ hτ x) =
      A.galAct τK (modelEquiv π A e he ι hι x) := by
  rw [modelEquiv_apply, modelEquiv_apply, ← genericEquiv_apply, ← genericEquiv_apply,
    ← genericEquiv_gal]
  congr 1
  apply Subtype.ext
  change specFrac R K ≫ Spec.map (CommRingCat.ofHom τ) ≫ x.1 =
    Spec.map (CommRingCat.ofHom (τK : K →+* K)) ≫ specFrac R K ≫ x.1
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext r
  exact hτK r

end Model

end ZInQ.Contrib.ColmezProperModel

end
