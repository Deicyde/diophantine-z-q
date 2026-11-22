import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! The split torus, represented by the localization of a polynomial ring at the product of its variables. -/

noncomputable section

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry Opposite MonObj
open ZInQ.HeightSplit ZInQ.SemiAbDescend

variable {k : Type} [Field k] {r : ℕ}

/-- The Laurent polynomial algebra represents tuples of units. -/
private def torusEval (R : Type) [CommRing R] [Algebra k R] :
    (TorusRing k r →ₐ[k] R) ≃ (Fin r → Rˣ) where
  toFun f i := Units.map (f : TorusRing k r →* R) (tUniv r i)
  invFun := torusLift
  left_inv _f := algHom_ext_torus _ _ (fun i => torusLift_tUniv _ i)
  right_inv t := funext fun i => Units.ext (torusLift_tUniv t i)

private theorem torusEval_natural {R S : Type} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (a : TorusRing k r →ₐ[k] R) :
    torusEval S (f.comp a) = fun i => Units.map (f : R →* S) (torusEval R a i) := by
  funext i
  apply Units.ext
  rfl

/-- The split torus of rank `r` over `k`. -/
abbrev splitTorus (k : Type) [Field k] (r : ℕ) : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (TorusRing k r)))

private def torusUnits (k : Type) [Field k] (r : ℕ) :
    (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ GrpCat :=
  let Γ := algΓ (CommRingCat.of k)
  { obj := fun X => GrpCat.of (Fin r → (Γ.obj X.unop).unopˣ)
    map := fun f => GrpCat.ofHom
      { toFun := fun t i => Units.map ((Γ.map f.unop).unop.hom : _ →* _) (t i)
        map_one' := by ext i; exact map_one _
        map_mul' := by intro a b; ext i; exact map_mul _ _ _ }
    map_id := by intro X; ext t i; simp
    map_comp := by intro X Y Z f g; ext t i; simp }

private def algHomEquiv {X Y : (CommAlgCat (CommRingCat.of k))ᵒᵖ} :
    (X ⟶ Y) ≃ (Y.unop →ₐ[k] X.unop) :=
  ⟨fun f => f.unop.hom, fun f => (CommAlgCat.ofHom f).op, fun _ => rfl, fun _ => rfl⟩

private def torusRep (k : Type) [Field k] (r : ℕ) :
    (torusUnits k r ⋙ forget GrpCat).RepresentableBy (splitTorus k r) where
  homEquiv {X} :=
    ((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv X _).symm.trans
      (algHomEquiv.trans (torusEval _))
  homEquiv_comp f g := by
    change torusEval _ (((algΓAlgSpecAdjunction _).homEquiv _ _).symm (f ≫ g)).unop.hom = _
    rw [Adjunction.homEquiv_naturality_left_symm (algΓAlgSpecAdjunction (CommRingCat.of k)) f g]
    exact torusEval_natural _ _

/-- The group law of the split torus is multiplication of its unit coordinates. -/
instance splitTorus.grpObj (k : Type) [Field k] (r : ℕ) : GrpObj (splitTorus k r) :=
  GrpObj.ofRepresentableBy _ (torusUnits k r) (torusRep k r)

private def torusGlobalPoints (X : Over (Spec (CommRingCat.of k))) :
    (X ⟶ splitTorus k r) ≃* (Fin r → ((algΓ (CommRingCat.of k)).obj X).unopˣ) where
  toEquiv := (torusRep k r).homEquiv
  map_mul' := ((yonedaGrpObjIsoOfRepresentableBy _ _ (torusRep k r)).hom.app (op X)).hom.map_mul

private def affineCounit (k : Type) [Field k] :
    algSpec (CommRingCat.of k) ⋙ algΓ (CommRingCat.of k) ≅ 𝟭 _ := by
  let α := algΓAlgSpecAdjunction (CommRingCat.of k)
  haveI : IsIso α.counit :=
    @Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ _ _ α
      algSpec.instFull algSpec.instFaithful
  exact asIso α.counit

/-- The `R`-points of the split torus are tuples of units of `R`. -/
def splitTorusPoints (R : Type) [CommRing R] [Algebra k R] :
    (algPt k R ⟶ splitTorus k r) ≃* (Fin r → Rˣ) :=
  (torusGlobalPoints _).trans
    (MulEquiv.piCongrRight fun _ =>
      Units.mapEquiv (CommAlgCat.algEquivOfIso
        (((affineCounit k).app (op (CommAlgCat.of k R))).unop.symm)).toRingEquiv.toMulEquiv)

/-- The point coordinates commute with change of the test algebra. -/
theorem splitTorusPoints_natural {R S : Type} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (p : algPt k R ⟶ splitTorus k r) :
    splitTorusPoints S (algPtMap f ≫ p) =
      fun i => Units.map (f : R →* S) (splitTorusPoints R p i) := by
  funext i
  apply Units.ext
  change ((affineCounit k).app
      (op (CommAlgCat.of k S))).inv.unop.hom
      ((torusRep k r).homEquiv (algPtMap f ≫ p) i).val =
    f (((affineCounit k).app
      (op (CommAlgCat.of k R))).inv.unop.hom ((torusRep k r).homEquiv p i).val)
  rw [(torusRep k r).homEquiv_comp]
  let X := op (CommAlgCat.of k S)
  let Y := ((algSpec (CommRingCat.of k) ⋙ algΓ (CommRingCat.of k)).obj
    (op (CommAlgCat.of k R)))
  have h := congrArg
    (fun (g : X ⟶ Y) => g.unop.hom ((torusRep k r).homEquiv p i).val)
    ((affineCounit k).inv.naturality (CommAlgCat.ofHom f).op)
  exact h.symm

end ZInQ.FaltingsRestate
