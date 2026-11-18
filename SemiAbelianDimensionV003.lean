import IdentityComponentDimensionV001
import FlatStalkDimensionV002
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# `dim U = a + t` at the identity, and `dim A = a + t`

Over an algebraically closed field `k`, let `U` be a group scheme locally of finite type with a
flat morphism `π : U → B` to an abelian variety `B` of dimension `a`. At the identity point `u`
(a closed point) the flat dimension formula gives
`dim 𝒪_{U,u} = dim 𝒪_{B,π u} + dim (𝒪_{U,u} / 𝔪_{π u} 𝒪_{U,u})`; group-scheme homogeneity
(statement form `GroupSchemeDimStalk`: the dimension of a group scheme locally of finite type over
a field is the dimension of its local ring at any closed point) turns the two outer terms into
`dim U` and `dim B = a`. So `dim U = a + t` once the closed-fibre local ring at the identity has
dimension `t` (`hfib`: the local ring at the identity of the scheme-theoretic kernel of `π`).
With the relative-dimension comparison of the generic fibre this gives `dim A = a + t`.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open IsLocalRing

namespace NeronRelativeDimension

/-- Statement form: a group scheme locally of finite type over a field has the dimension of its
local ring at every closed point. -/
def GroupSchemeDimStalk : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] (g : G.left), IsClosed ({g} : Set G.left) →
      topologicalKrullDim G.left = ringKrullDim (G.left.presheaf.stalk g)

/-- The identity point of a group scheme over a field. -/
def idPt {k : Type} [Field k] (X : Over (Spec (CommRingCat.of k))) [GrpObj X] : X.left :=
  (η[X] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X).left (IsLocalRing.closedPoint k)

/-- **`dim U = a + t`** from the flat dimension formula at the identity. -/
theorem dim_identityComponent_eq_add (hHom : GroupSchemeDimStalk) {k : Type} [Field k]
    [IsAlgClosed k] (U : Over (Spec (CommRingCat.of k))) [GrpObj U] [LocallyOfFiniteType U.hom]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [Flat π.left] (a t : ℕ)
    (hB : topologicalKrullDim B.X.left = (a : WithBot ℕ∞))
    (hfib : letI := (π.left.stalkMap (idPt U)).hom.toAlgebra
      ringKrullDim (U.left.presheaf.stalk (idPt U) ⧸
        (maximalIdeal (B.X.left.presheaf.stalk (π.left (idPt U)))).map
          (algebraMap (B.X.left.presheaf.stalk (π.left (idPt U)))
            (U.left.presheaf.stalk (idPt U)))) = (t : WithBot ℕ∞)) :
    topologicalKrullDim U.left = ((a + t : ℕ) : WithBot ℕ∞) := by
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  have hsec : (η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left ≫ U.hom = 𝟙 _ := Over.w _
  have hsec' : ((η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left ≫ π.left) ≫ B.X.hom =
      𝟙 _ := by
    rw [Category.assoc, Over.w π]
    exact hsec
  have hu : IsClosed ({idPt U} : Set U.left) :=
    mem_closedPoints_iff.mp (pointEquivClosedPoint U.hom ⟨_, hsec⟩).2
  have hb : IsClosed ({π.left (idPt U)} : Set B.X.left) := by
    have h := mem_closedPoints_iff.mp (pointEquivClosedPoint B.X.hom ⟨_, hsec'⟩).2
    exact h
  rw [hHom k U (idPt U) hu, FlatDimension.stalk_dim_eq_add_of_flat π.left (idPt U),
    ← hHom k B.X (π.left (idPt U)) hb, hB, hfib]
  push_cast
  rfl

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- **`dim A = a + t`** for the generic fibre of a smooth group model whose geometric fibre has
an open subgroup `U` with a flat map `π : U → B` to an abelian variety of dimension `a`, given the
closed-fibre local dimension `t` at the identity. -/
theorem dim_generic_eq_add (hV1 : SmoothGroupRelDimLocal) (hV3 : SmoothRelDimKrullDim)
    (hHom : GroupSchemeDimStalk)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (e : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] [IsAlgClosed k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N) [IsOpenImmersion inc.left]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [Flat π.left] (a t : ℕ)
    (hB : topologicalKrullDim B.X.left = (a : WithBot ℕ∞))
    (hfib : letI := (π.left.stalkMap (idPt U)).hom.toAlgebra
      ringKrullDim (U.left.presheaf.stalk (idPt U) ⧸
        (maximalIdeal (B.X.left.presheaf.stalk (π.left (idPt U)))).map
          (algebraMap (B.X.left.presheaf.stalk (π.left (idPt U)))
            (U.left.presheaf.stalk (idPt U)))) = (t : WithBot ℕ∞)) :
    topologicalKrullDim A.X.left = ((a + t : ℕ) : WithBot ℕ∞) := by
  have : LocallyOfFiniteType U.hom := by
    have hG : LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N).hom := by
      change LocallyOfFiniteType (pullback.snd N.hom _)
      infer_instance
    have h : inc.left ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N).hom = U.hom :=
      Over.w inc
    rw [← h]
    infer_instance
  exact dim_eq_add_of_extension_dim hV1 hV3 N e φ U inc a t
    (dim_identityComponent_eq_add hHom U B π a t hB hfib)

end NeronRelativeDimension
