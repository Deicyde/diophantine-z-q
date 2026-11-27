import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.PacketOfLeaves
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
set_option autoImplicit false
namespace Y3Buzzard

/-!
# Compatibility of the diagonal action with multiplication (draft)

`ActionMulCompat` from the leaf `ZeroPreservingIsHom` (Milne, Abelian Varieties, Storrs
article, Cor. 20.2(a)). The comparison map `actionTot M d`, lying over `g = actionMap M d`,
factors as a map `theta : A ⟶ g^* A` in `Over X`. It preserves the unit, so it is a
homomorphism by the leaf. Its multiplicativity, projected along `g^* A ⟶ A`, is
`psi ≫ mulL = mulL ≫ actionTot`, where `psi` acts componentwise on `A x_X A` by `actionTot`.
The universal property of the fibre-power square identifies `psi` with `actAA`.
-/

attribute [local instance] FEC.grp

/-- B4'' over a locally noetherian base: a morphism of false elliptic curves carrying the unit
section to the unit section is a homomorphism. This is a special case of J. S. Milne, *Abelian
Varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic Geometry*, Springer (1986),
Cor. 20.2(a), p. 43 of the author's retyped edition: "Every morphism of abelian schemes carrying
the zero section into the zero section is a homomorphism." Its proof applies the rigidity lemma,
Prop. 20.1, which is stated for a connected base. The same statement, over an arbitrary base, is
K.-W. Lan, *Arithmetic Compactifications of PEL-Type Shimura Varieties*, Harvard thesis (2008),
Cor. 1.3.1.6 (for a separated target in its 2021 revision), citing GIT, Cor. 6.4. -/
def ZeroPreservingIsHomLN : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : FEC S) (f : A.F ⟶ A'.F),
    letI := A.grp
    letI := A'.grp
    (MonObj.one : 𝟙_ (Over S) ⟶ A.F) ≫ f = MonObj.one → IsMonHom f

theorem zeroPreservingIsHomLN_of (h : ZeroPreservingIsHom) : ZeroPreservingIsHomLN :=
  fun S _ A A' f hf => h S A A' f hf


/-! ## 1. Generic facts on `Over.pullback` -/

section Generic

variable {S S' : Scheme.{0}}

theorem pullback_one_eq (A : FEC S) (g : S' ⟶ S) :
    (MonObj.one : 𝟙_ (Over S') ⟶ (A.pullback g).F) =
      Functor.LaxMonoidal.ε (Over.pullback g) ≫
        (Over.pullback g).map (MonObj.one : 𝟙_ (Over S) ⟶ A.F) := by
  first
    | rfl
    | exact Functor.obj.η_def (F := Over.pullback g) A.F

theorem pullback_mul_eq (A : FEC S) (g : S' ⟶ S) :
    (MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F) =
      Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F ≫
        (Over.pullback g).map (MonObj.mul : A.F ⊗ A.F ⟶ A.F) := by
  first
    | rfl
    | exact Functor.obj.μ_def (F := Over.pullback g) A.F

theorem pullbackF_hom_ext (A : FEC S) (g : S' ⟶ S) {U : Over S'}
    {f f' : U ⟶ (A.pullback g).F}
    (h : f.left ≫ A.pullbackFst g = f'.left ≫ A.pullbackFst g) : f = f' :=
  Over.OverMorphism.ext
    (pullback.hom_ext (f := A.F.hom) (g := g) h ((Over.w f).trans (Over.w f').symm))

theorem eps_left_fst (g : S' ⟶ S) :
    (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
      pullback.fst (𝟙_ (Over S)).hom g = g :=
  calc (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ pullback.fst (𝟙_ (Over S)).hom g
      = ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over S)).hom g) ≫ (𝟙_ (Over S)).hom :=
        (Category.comp_id _).symm
    _ = (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          (pullback.fst (𝟙_ (Over S)).hom g ≫ (𝟙_ (Over S)).hom) :=
        Category.assoc _ _ _
    _ = (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          (pullback.snd (𝟙_ (Over S)).hom g ≫ g) :=
        congrArg (fun k => (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ k)
          (pullback.condition (f := (𝟙_ (Over S)).hom) (g := g))
    _ = ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.snd (𝟙_ (Over S)).hom g) ≫ g :=
        (Category.assoc _ _ _).symm
    _ = 𝟙 S' ≫ g :=
        congrArg (fun k => k ≫ g) (Over.w (Functor.LaxMonoidal.ε (Over.pullback g)))
    _ = g := Category.id_comp g

/-- Maps into the total space of a binary product in `Over S` are determined by their
two components. -/
theorem tensor_left_ext {U V : Over S} {T : Scheme.{0}} {u v : T ⟶ (U ⊗ V).left}
    (h1 : u ≫ (CartesianMonoidalCategory.fst U V).left =
      v ≫ (CartesianMonoidalCategory.fst U V).left)
    (h2 : u ≫ (CartesianMonoidalCategory.snd U V).left =
      v ≫ (CartesianMonoidalCategory.snd U V).left) : u = v := by
  have hw : v ≫ (U ⊗ V).hom = u ≫ (U ⊗ V).hom :=
    calc v ≫ (U ⊗ V).hom
        = v ≫ ((CartesianMonoidalCategory.fst U V).left ≫ U.hom) :=
          congrArg (fun k => v ≫ k) (Over.w (CartesianMonoidalCategory.fst U V)).symm
      _ = (v ≫ (CartesianMonoidalCategory.fst U V).left) ≫ U.hom :=
          (Category.assoc _ _ _).symm
      _ = (u ≫ (CartesianMonoidalCategory.fst U V).left) ≫ U.hom :=
          congrArg (fun k => k ≫ U.hom) h1.symm
      _ = u ≫ ((CartesianMonoidalCategory.fst U V).left ≫ U.hom) := Category.assoc _ _ _
      _ = u ≫ (U ⊗ V).hom :=
          congrArg (fun k => u ≫ k) (Over.w (CartesianMonoidalCategory.fst U V))
  let fu : Over.mk (u ≫ (U ⊗ V).hom) ⟶ U ⊗ V := Over.homMk u rfl
  let fv : Over.mk (u ≫ (U ⊗ V).hom) ⟶ U ⊗ V := Over.homMk v hw
  have e1 : fu ≫ CartesianMonoidalCategory.fst U V = fv ≫ CartesianMonoidalCategory.fst U V :=
    Over.OverMorphism.ext h1
  have e2 : fu ≫ CartesianMonoidalCategory.snd U V = fv ≫ CartesianMonoidalCategory.snd U V :=
    Over.OverMorphism.ext h2
  have e : fu = fv := by
    first
      | exact CartesianMonoidalCategory.hom_ext _ _ e1 e2
      | exact CartesianMonoidalCategory.hom_ext e1 e2
      | (ext1 <;> assumption)
  exact congrArg (fun f => f.left) e

theorem pb_mu_fst {X Y : Scheme.{0}} (q : X ⟶ Y) (U V : Over Y) :
    Functor.LaxMonoidal.μ (Over.pullback q) U V ≫
        (Over.pullback q).map (CartesianMonoidalCategory.fst U V) =
      CartesianMonoidalCategory.fst ((Over.pullback q).obj U) ((Over.pullback q).obj V) := by
  first
    | exact Functor.Monoidal.μ_fst (Over.pullback q) U V
    | exact Functor.Monoidal.μ_fst U V
    | exact Functor.Monoidal.μ_fst ..
    | exact (congrArg (fun k => Functor.LaxMonoidal.μ (Over.pullback q) U V ≫ k)
        (Functor.OplaxMonoidal.δ_fst (Over.pullback q) U V).symm).trans
        (Functor.Monoidal.μ_δ_assoc ..)
    | exact (congrArg (fun k => Functor.LaxMonoidal.μ (Over.pullback q) U V ≫ k)
        (CartesianMonoidalCategory.prodComparison_fst (Over.pullback q) U V).symm).trans
        (Functor.Monoidal.μ_δ_assoc ..)
    | simp

theorem pb_mu_snd {X Y : Scheme.{0}} (q : X ⟶ Y) (U V : Over Y) :
    Functor.LaxMonoidal.μ (Over.pullback q) U V ≫
        (Over.pullback q).map (CartesianMonoidalCategory.snd U V) =
      CartesianMonoidalCategory.snd ((Over.pullback q).obj U) ((Over.pullback q).obj V) := by
  first
    | exact Functor.Monoidal.μ_snd (Over.pullback q) U V
    | exact Functor.Monoidal.μ_snd U V
    | exact Functor.Monoidal.μ_snd ..
    | exact (congrArg (fun k => Functor.LaxMonoidal.μ (Over.pullback q) U V ≫ k)
        (Functor.OplaxMonoidal.δ_snd (Over.pullback q) U V).symm).trans
        (Functor.Monoidal.μ_δ_assoc ..)
    | exact (congrArg (fun k => Functor.LaxMonoidal.μ (Over.pullback q) U V ≫ k)
        (CartesianMonoidalCategory.prodComparison_snd (Over.pullback q) U V).symm).trans
        (Functor.Monoidal.μ_δ_assoc ..)
    | simp

/-- First component of `(α ⊗ β) ≫ μ`, read on total spaces. -/
theorem pb_tensor_fst {X Y : Scheme.{0}} (q : X ⟶ Y) {U V : Over Y} {U' V' : Over X}
    (α : U' ⟶ (Over.pullback q).obj U) (β : V' ⟶ (Over.pullback q).obj V) :
    ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫
        pullback.fst (U ⊗ V).hom q ≫ (CartesianMonoidalCategory.fst U V).left =
      (CartesianMonoidalCategory.fst U' V').left ≫ α.left ≫ pullback.fst U.hom q := by
  have e2 : (α ⊗ₘ β) ≫ CartesianMonoidalCategory.fst ((Over.pullback q).obj U)
      ((Over.pullback q).obj V) = CartesianMonoidalCategory.fst U' V' ≫ α := by
    first
      | exact CartesianMonoidalCategory.tensorHom_fst α β
      | exact CartesianMonoidalCategory.tensorHom_fst ..
      | simp
  have e3 : ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V) ≫
      (Over.pullback q).map (CartesianMonoidalCategory.fst U V) =
        CartesianMonoidalCategory.fst U' V' ≫ α :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (α ⊗ₘ β) ≫ k) (pb_mu_fst q U V)).trans e2)
  calc ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫
        pullback.fst (U ⊗ V).hom q ≫ (CartesianMonoidalCategory.fst U V).left
      = ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫
          ((Over.pullback q).map (CartesianMonoidalCategory.fst U V)).left ≫
            pullback.fst U.hom q :=
        congrArg (fun k => ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫ k)
          (map_left_fst q (CartesianMonoidalCategory.fst U V)).symm
    _ = (((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V) ≫
          (Over.pullback q).map (CartesianMonoidalCategory.fst U V)).left ≫
            pullback.fst U.hom q :=
        (Category.assoc ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left
          ((Over.pullback q).map (CartesianMonoidalCategory.fst U V)).left
          (pullback.fst U.hom q)).symm
    _ = (CartesianMonoidalCategory.fst U' V' ≫ α).left ≫ pullback.fst U.hom q :=
        congrArg (fun k => k.left ≫ pullback.fst U.hom q) e3
    _ = (CartesianMonoidalCategory.fst U' V').left ≫ α.left ≫ pullback.fst U.hom q :=
        Category.assoc (CartesianMonoidalCategory.fst U' V').left α.left (pullback.fst U.hom q)

/-- Second component of `(α ⊗ β) ≫ μ`, read on total spaces. -/
theorem pb_tensor_snd {X Y : Scheme.{0}} (q : X ⟶ Y) {U V : Over Y} {U' V' : Over X}
    (α : U' ⟶ (Over.pullback q).obj U) (β : V' ⟶ (Over.pullback q).obj V) :
    ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫
        pullback.fst (U ⊗ V).hom q ≫ (CartesianMonoidalCategory.snd U V).left =
      (CartesianMonoidalCategory.snd U' V').left ≫ β.left ≫ pullback.fst V.hom q := by
  have e2 : (α ⊗ₘ β) ≫ CartesianMonoidalCategory.snd ((Over.pullback q).obj U)
      ((Over.pullback q).obj V) = CartesianMonoidalCategory.snd U' V' ≫ β := by
    first
      | exact CartesianMonoidalCategory.tensorHom_snd α β
      | exact CartesianMonoidalCategory.tensorHom_snd ..
      | simp
  have e3 : ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V) ≫
      (Over.pullback q).map (CartesianMonoidalCategory.snd U V) =
        CartesianMonoidalCategory.snd U' V' ≫ β :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (α ⊗ₘ β) ≫ k) (pb_mu_snd q U V)).trans e2)
  calc ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫
        pullback.fst (U ⊗ V).hom q ≫ (CartesianMonoidalCategory.snd U V).left
      = ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫
          ((Over.pullback q).map (CartesianMonoidalCategory.snd U V)).left ≫
            pullback.fst V.hom q :=
        congrArg (fun k => ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left ≫ k)
          (map_left_fst q (CartesianMonoidalCategory.snd U V)).symm
    _ = (((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V) ≫
          (Over.pullback q).map (CartesianMonoidalCategory.snd U V)).left ≫
            pullback.fst V.hom q :=
        (Category.assoc ((α ⊗ₘ β) ≫ Functor.LaxMonoidal.μ (Over.pullback q) U V).left
          ((Over.pullback q).map (CartesianMonoidalCategory.snd U V)).left
          (pullback.fst V.hom q)).symm
    _ = (CartesianMonoidalCategory.snd U' V' ≫ β).left ≫ pullback.fst V.hom q :=
        congrArg (fun k => k.left ≫ pullback.fst V.hom q) e3
    _ = (CartesianMonoidalCategory.snd U' V').left ≫ β.left ≫ pullback.fst V.hom q :=
        Category.assoc (CartesianMonoidalCategory.snd U' V').left β.left (pullback.fst V.hom q)

end Generic

/-! ## 2. A map over `g` as a map into the base change -/

section Theta

variable {S : Scheme.{0}} (A : FEC S) (g : S ⟶ S) (t : A.F.left ⟶ A.F.left)
  (ht : t ≫ A.F.hom = A.F.hom ≫ g)

/-- `t`, lying over `g`, as a map `A ⟶ g^* A` in `Over S`. -/
def thetaOf : A.F ⟶ (A.pullback g).F :=
  Over.homMk (pullback.lift t A.F.hom ht : A.F.left ⟶ pullback A.F.hom g)
    (pullback.lift_snd t A.F.hom ht)

theorem thetaOf_fst : (thetaOf A g t ht).left ≫ A.pullbackFst g = t :=
  pullback.lift_fst t A.F.hom ht

/-- `thetaOf` preserves the unit when `t` does. -/
theorem thetaOf_one (h1 : g ≫ oneL A = oneL A ≫ t) :
    (MonObj.one : 𝟙_ (Over S) ⟶ A.F) ≫ thetaOf A g t ht =
      (MonObj.one : 𝟙_ (Over S) ⟶ (A.pullback g).F) := by
  apply pullbackF_hom_ext A g
  have hε := eps_left_fst g
  have hm := map_left_fst g (MonObj.one : 𝟙_ (Over S) ⟶ A.F)
  calc ((MonObj.one : 𝟙_ (Over S) ⟶ A.F) ≫ thetaOf A g t ht).left ≫ A.pullbackFst g
      = oneL A ≫ ((thetaOf A g t ht).left ≫ A.pullbackFst g) :=
        Category.assoc (oneL A) (thetaOf A g t ht).left (A.pullbackFst g)
    _ = oneL A ≫ t := congrArg (fun k => oneL A ≫ k) (thetaOf_fst A g t ht)
    _ = g ≫ oneL A := h1.symm
    _ = ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over S)).hom g) ≫ oneL A :=
        congrArg (fun k => k ≫ oneL A) hε.symm
    _ = (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          (pullback.fst (𝟙_ (Over S)).hom g ≫ oneL A) :=
        Category.assoc _ _ _
    _ = (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          (((Over.pullback g).map (MonObj.one : 𝟙_ (Over S) ⟶ A.F)).left ≫
            pullback.fst A.F.hom g) :=
        congrArg (fun k => (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ k) hm.symm
    _ = (Functor.LaxMonoidal.ε (Over.pullback g) ≫
          (Over.pullback g).map (MonObj.one : 𝟙_ (Over S) ⟶ A.F)).left ≫ A.pullbackFst g :=
        (Category.assoc (Functor.LaxMonoidal.ε (Over.pullback g)).left
          ((Over.pullback g).map (MonObj.one : 𝟙_ (Over S) ⟶ A.F)).left
          (pullback.fst A.F.hom g)).symm
    _ = (MonObj.one : 𝟙_ (Over S) ⟶ (A.pullback g).F).left ≫ A.pullbackFst g :=
        congrArg (fun k => k.left ≫ A.pullbackFst g) (pullback_one_eq A g).symm

theorem thetaOf_isMonHom (hB4 : ZeroPreservingIsHomLN) [IsLocallyNoetherian S]
    (h1 : g ≫ oneL A = oneL A ≫ t) :
    IsMonHom (thetaOf A g t ht) :=
  hB4 S A (A.pullback g) (thetaOf A g t ht) (thetaOf_one A g t ht h1)

/-- The induced map on `A x_S A`, lying over `g`. -/
def psiOf : (A.F ⊗ A.F).left ⟶ (A.F ⊗ A.F).left :=
  ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
      Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫
    pullback.fst (A.F ⊗ A.F).hom g

/-- The multiplication of the base change, projected to `A`. -/
theorem mul_left_fst :
    (MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F).left ≫ A.pullbackFst g =
      (Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫ (pullback.fst (A.F ⊗ A.F).hom g ≫ mulL A) := by
  have h1 : (MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F).left =
      (Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫ ((Over.pullback g).map (MonObj.mul : A.F ⊗ A.F ⟶ A.F)).left :=
    congrArg (fun k => k.left) (pullback_mul_eq A g)
  have h2 : ((Over.pullback g).map (MonObj.mul : A.F ⊗ A.F ⟶ A.F)).left ≫ A.pullbackFst g = pullback.fst (A.F ⊗ A.F).hom g ≫ mulL A :=
    map_left_fst g (MonObj.mul : A.F ⊗ A.F ⟶ A.F)
  exact (congrArg (fun k => k ≫ A.pullbackFst g) h1).trans
    ((Category.assoc (Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ((Over.pullback g).map (MonObj.mul : A.F ⊗ A.F ⟶ A.F)).left
        (A.pullbackFst g)).trans
      (congrArg (fun k => (Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫ k) h2))

/-- Multiplicativity of `thetaOf`, projected to `A`. -/
theorem mulL_comp_of_isMonHom (hθ : IsMonHom (thetaOf A g t ht)) :
    mulL A ≫ t = psiOf A g t ht ≫ mulL A := by
  haveI := hθ
  have hmul : (MonObj.mul : A.F ⊗ A.F ⟶ A.F) ≫ thetaOf A g t ht = (thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫ (MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F) := by
    first
      | exact IsMonHom.mul_hom (thetaOf A g t ht)
      | exact IsMonHom.mul_hom (f := thetaOf A g t ht)
  have e1 : mulL A ≫ t = ((MonObj.mul : A.F ⊗ A.F ⟶ A.F) ≫ thetaOf A g t ht).left ≫ A.pullbackFst g :=
    (congrArg (fun k => mulL A ≫ k) (thetaOf_fst A g t ht)).symm.trans
      (Category.assoc (mulL A) (thetaOf A g t ht).left (A.pullbackFst g)).symm
  have e2 : ((MonObj.mul : A.F ⊗ A.F ⟶ A.F) ≫ thetaOf A g t ht).left ≫ A.pullbackFst g =
      ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫ (MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F)).left ≫ A.pullbackFst g :=
    congrArg (fun k => k.left ≫ A.pullbackFst g) hmul
  have e3 : ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫ (MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F)).left ≫ A.pullbackFst g =
      (thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left ≫ ((MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F).left ≫ A.pullbackFst g) :=
    Category.assoc (thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left (MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F).left (A.pullbackFst g)
  have e4 : (thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left ≫ ((MonObj.mul : (A.pullback g).F ⊗ (A.pullback g).F ⟶ (A.pullback g).F).left ≫ A.pullbackFst g) =
      (thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left ≫ ((Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫ (pullback.fst (A.F ⊗ A.F).hom g ≫ mulL A)) :=
    congrArg (fun k => (thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left ≫ k) (mul_left_fst A g)
  have e5 : (thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left ≫ ((Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫ (pullback.fst (A.F ⊗ A.F).hom g ≫ mulL A)) =
      (((thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left ≫ (Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left) ≫ pullback.fst (A.F ⊗ A.F).hom g) ≫ mulL A :=
    (Category.assoc (thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left (Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left (pullback.fst (A.F ⊗ A.F).hom g ≫ mulL A)).symm.trans
      (Category.assoc ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht).left ≫ (Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left) (pullback.fst (A.F ⊗ A.F).hom g) (mulL A)).symm
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem psiOf_fst :
    psiOf A g t ht ≫ (CartesianMonoidalCategory.fst A.F A.F).left =
      (CartesianMonoidalCategory.fst A.F A.F).left ≫ t :=
  calc psiOf A g t ht ≫ (CartesianMonoidalCategory.fst A.F A.F).left
      = ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
          Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫
          pullback.fst (A.F ⊗ A.F).hom g ≫ (CartesianMonoidalCategory.fst A.F A.F).left :=
        Category.assoc _ _ _
    _ = (CartesianMonoidalCategory.fst A.F A.F).left ≫
          (thetaOf A g t ht).left ≫ pullback.fst A.F.hom g :=
        pb_tensor_fst g (U := A.F) (V := A.F) (thetaOf A g t ht) (thetaOf A g t ht)
    _ = (CartesianMonoidalCategory.fst A.F A.F).left ≫ t :=
        congrArg (fun k => (CartesianMonoidalCategory.fst A.F A.F).left ≫ k)
          (thetaOf_fst A g t ht)

theorem psiOf_snd :
    psiOf A g t ht ≫ (CartesianMonoidalCategory.snd A.F A.F).left =
      (CartesianMonoidalCategory.snd A.F A.F).left ≫ t :=
  calc psiOf A g t ht ≫ (CartesianMonoidalCategory.snd A.F A.F).left
      = ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
          Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫
          pullback.fst (A.F ⊗ A.F).hom g ≫ (CartesianMonoidalCategory.snd A.F A.F).left :=
        Category.assoc _ _ _
    _ = (CartesianMonoidalCategory.snd A.F A.F).left ≫
          (thetaOf A g t ht).left ≫ pullback.fst A.F.hom g :=
        pb_tensor_snd g (U := A.F) (V := A.F) (thetaOf A g t ht) (thetaOf A g t ht)
    _ = (CartesianMonoidalCategory.snd A.F A.F).left ≫ t :=
        congrArg (fun k => (CartesianMonoidalCategory.snd A.F A.F).left ≫ k)
          (thetaOf_fst A g t ht)

theorem psiOf_hom : psiOf A g t ht ≫ (A.F ⊗ A.F).hom = (A.F ⊗ A.F).hom ≫ g := by
  have hw := Over.w ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
    Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F)
  calc psiOf A g t ht ≫ (A.F ⊗ A.F).hom
      = ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
          Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫
          (pullback.fst (A.F ⊗ A.F).hom g ≫ (A.F ⊗ A.F).hom) :=
        Category.assoc _ _ _
    _ = ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
          Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫
          (pullback.snd (A.F ⊗ A.F).hom g ≫ g) :=
        congrArg (fun k => ((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
          Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫ k)
          (pullback.condition (f := (A.F ⊗ A.F).hom) (g := g))
    _ = (((thetaOf A g t ht ⊗ₘ thetaOf A g t ht) ≫
          Functor.LaxMonoidal.μ (Over.pullback g) A.F A.F).left ≫
          pullback.snd (A.F ⊗ A.F).hom g) ≫ g :=
        (Category.assoc _ _ _).symm
    _ = (A.F ⊗ A.F).hom ≫ g := congrArg (fun k => k ≫ g) hw

end Theta

/-! ## 3. Components of the fibre-power map -/

section FibrePowerComp

variable {X Y B : Scheme.{0}} (A : FEC X) (qX : X ⟶ Y) (qA : A.F.left ⟶ B) (b : B ⟶ Y)
  (hpb : IsPullback qA A.F.hom b qX)

theorem sqTensorIsoOf_inv : (sqTensorIsoOf A qX qA b hpb).inv =
    ((sqIsoOf A qX qA b hpb).hom ⊗ₘ (sqIsoOf A qX qA b hpb).hom) ≫
      Functor.LaxMonoidal.μ (Over.pullback qX) (Over.mk b) (Over.mk b) := by
  first
    | rfl
    | simp [sqTensorIsoOf]

theorem fibrePowerMap_eq : fibrePowerMap A qX qA b hpb =
    (sqTensorIsoOf A qX qA b hpb).inv.left ≫ pullback.fst (Over.mk b ⊗ Over.mk b).hom qX :=
  rfl

theorem sqIsoOf_hom_fst :
    (sqIsoOf A qX qA b hpb).hom.left ≫ pullback.fst (Over.mk b).hom qX = qA :=
  hpb.isoPullback_hom_fst

theorem fibrePowerMap_fst :
    fibrePowerMap A qX qA b hpb ≫ (CartesianMonoidalCategory.fst (Over.mk b) (Over.mk b)).left =
      (CartesianMonoidalCategory.fst A.F A.F).left ≫ qA := by
  have s1 := pb_tensor_fst qX (U := Over.mk b) (V := Over.mk b) (sqIsoOf A qX qA b hpb).hom
    (sqIsoOf A qX qA b hpb).hom
  rw [fibrePowerMap_eq, Category.assoc, sqTensorIsoOf_inv, s1, sqIsoOf_hom_fst]

theorem fibrePowerMap_snd :
    fibrePowerMap A qX qA b hpb ≫ (CartesianMonoidalCategory.snd (Over.mk b) (Over.mk b)).left =
      (CartesianMonoidalCategory.snd A.F A.F).left ≫ qA := by
  have s1 := pb_tensor_snd qX (U := Over.mk b) (V := Over.mk b) (sqIsoOf A qX qA b hpb).hom
    (sqIsoOf A qX qA b hpb).hom
  rw [fibrePowerMap_eq, Category.assoc, sqTensorIsoOf_inv, s1, sqIsoOf_hom_fst]

end FibrePowerComp

/-! ## 4. Identification with `actAA` and the main theorem -/

theorem actionTot_qA (M : Moduli35) (Q : QuotientData M) (d : Y3OrderMod.G 5) :
    actionTot M d ≫ Q.qA = Q.qA := by
  first
    | exact act_comp_eq (ρA M) Q.kpA d
    | exact (congrArg (fun k => k ≫ Q.qA) (ι_actS (ρA M) d)).symm.trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => Sigma.ι (fun _ : Y3OrderMod.G 5 => M.A.F.left) d ≫ k)
            Q.kpA.w).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun k => k ≫ Q.qA) (ι_actT M.A.F.left d)).trans
                (Category.id_comp _)))))

theorem psiOf_eq_actAA (M : Moduli35) (Q : QuotientData M) (d : Y3OrderMod.G 5) :
    psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) = actAA M Q d := by
  have hinv := actionTot_qA M Q d
  have hF1 := fibrePowerMap_fst M.A Q.qX Q.qA Q.b Q.cart
  have hF2 := fibrePowerMap_snd M.A Q.qX Q.qA Q.b Q.cart
  have hP1 := psiOf_fst M.A (actionMap M d).left (actionTot M d) (actionTot_w M d)
  have hP2 := psiOf_snd M.A (actionMap M d).left (actionTot M d) (actionTot_w M d)
  apply (fibrePowerMap_isPullback M.A Q.qX Q.qA Q.b Q.cart).hom_ext
  · refine Eq.trans ?_ (actAA_q M Q d).symm
    refine tensor_left_ext ?_ ?_
    · calc (psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
            fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart) ≫
            (CartesianMonoidalCategory.fst (Over.mk Q.b) (Over.mk Q.b)).left
          = psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
              (fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart ≫
                (CartesianMonoidalCategory.fst (Over.mk Q.b) (Over.mk Q.b)).left) :=
            Category.assoc _ _ _
        _ = psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
              ((CartesianMonoidalCategory.fst M.A.F M.A.F).left ≫ Q.qA) :=
            congrArg (fun k => psiOf M.A (actionMap M d).left (actionTot M d)
              (actionTot_w M d) ≫ k) hF1
        _ = (psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
              (CartesianMonoidalCategory.fst M.A.F M.A.F).left) ≫ Q.qA :=
            (Category.assoc _ _ _).symm
        _ = ((CartesianMonoidalCategory.fst M.A.F M.A.F).left ≫ actionTot M d) ≫ Q.qA :=
            congrArg (fun k => k ≫ Q.qA) hP1
        _ = (CartesianMonoidalCategory.fst M.A.F M.A.F).left ≫ (actionTot M d ≫ Q.qA) :=
            Category.assoc _ _ _
        _ = (CartesianMonoidalCategory.fst M.A.F M.A.F).left ≫ Q.qA :=
            congrArg (fun k => (CartesianMonoidalCategory.fst M.A.F M.A.F).left ≫ k) hinv
        _ = fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart ≫
              (CartesianMonoidalCategory.fst (Over.mk Q.b) (Over.mk Q.b)).left :=
            hF1.symm
    · calc (psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
            fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart) ≫
            (CartesianMonoidalCategory.snd (Over.mk Q.b) (Over.mk Q.b)).left
          = psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
              (fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart ≫
                (CartesianMonoidalCategory.snd (Over.mk Q.b) (Over.mk Q.b)).left) :=
            Category.assoc _ _ _
        _ = psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
              ((CartesianMonoidalCategory.snd M.A.F M.A.F).left ≫ Q.qA) :=
            congrArg (fun k => psiOf M.A (actionMap M d).left (actionTot M d)
              (actionTot_w M d) ≫ k) hF2
        _ = (psiOf M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) ≫
              (CartesianMonoidalCategory.snd M.A.F M.A.F).left) ≫ Q.qA :=
            (Category.assoc _ _ _).symm
        _ = ((CartesianMonoidalCategory.snd M.A.F M.A.F).left ≫ actionTot M d) ≫ Q.qA :=
            congrArg (fun k => k ≫ Q.qA) hP2
        _ = (CartesianMonoidalCategory.snd M.A.F M.A.F).left ≫ (actionTot M d ≫ Q.qA) :=
            Category.assoc _ _ _
        _ = (CartesianMonoidalCategory.snd M.A.F M.A.F).left ≫ Q.qA :=
            congrArg (fun k => (CartesianMonoidalCategory.snd M.A.F M.A.F).left ≫ k) hinv
        _ = fibrePowerMap M.A Q.qX Q.qA Q.b Q.cart ≫
              (CartesianMonoidalCategory.snd (Over.mk Q.b) (Over.mk Q.b)).left :=
            hF2.symm
  · exact (psiOf_hom M.A (actionMap M d).left (actionTot M d) (actionTot_w M d)).trans
      ((congrArg (fun k => (M.A.F ⊗ M.A.F).hom ≫ k) (ρ_hom M d)).symm.trans
        (actAA_hom M Q d).symm)

/-- `ActionMulCompatLN` from the leaf B4'' over a locally noetherian base (Milne, Storrs
article, Cor. 20.2(a)). -/
theorem actionMulCompatLN_of_B4 (hB4 : ZeroPreservingIsHomLN) : ActionMulCompatLN := by
  unfold ActionMulCompatLN
  intro M Q hLN d
  haveI := hLN
  have h := mulL_comp_of_isMonHom M.A (actionMap M d).left (actionTot M d) (actionTot_w M d)
    (thetaOf_isMonHom M.A (actionMap M d).left (actionTot M d) (actionTot_w M d) hB4
      (actionTot_oneL M d))
  exact (congrArg (fun k => k ≫ mulL M.A) (psiOf_eq_actAA M Q d)).symm.trans h.symm

end Y3Buzzard
