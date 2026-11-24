import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Multiplication on the actual residue-field fibre of an abelian scheme

The object used throughout is exactly `Over.pullback.mapGrp.obj` applied to the
canonical morphism `Spec κ(s) ⟶ Spec O`. In particular, neither the fibre's carrier
nor its group law is replaced by an isomorphic model. Powers below are powers in
`MonObj.Hom.group`, not iterates under composition.

This module supplies the object, morphism, scalar, and geometry bridges for
`AvSplit.T4.MulEtaleAbelianScheme`. It does not assert that leaf or import a proof
of flatness or étaleness of multiplication.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace ZInQ.Contrib.MulEtale.FibreMaps

variable {O : Type} [CommRing O]

/-- The native residue-field group object, with its native transported group law. -/
abbrev fibreGrp (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O)) :
    Grp (Over (Spec ((Spec (.of O)).residueField s))) :=
  (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).mapGrp.obj A

/-- No comparison isomorphism is involved in identifying the underlying scheme. -/
theorem fibreGrp_left (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O)) :
    (fibreGrp A s).X.left = A.X.hom.fiber s := rfl

/-- The native structure map is exactly the canonical fibre-to-residue-field map. -/
theorem fibreGrp_hom (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O)) :
    (fibreGrp A s).X.hom = A.X.hom.fiberToSpecResidueField s := rfl

/-- Base change preserves the actual identity map. -/
theorem pullback_id (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O)) :
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map (𝟙 A.X) =
      𝟙 (fibreGrp A s).X :=
  (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map_id A.X

/-- Base change preserves the constant unit map (including the zero-power case). -/
theorem pullback_one (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (T : Over (Spec (.of O))) :
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map (1 : T ⟶ A.X) = 1 :=
  Functor.map_one _

/-- Base change preserves the pointwise operation on maps into the group object. -/
theorem pullback_mul (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (T : Over (Spec (.of O))) (f g : T ⟶ A.X) :
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map (f * g) =
      (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map f *
        (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map g :=
  Functor.map_mul _ f g

/-- Base change preserves pointwise natural powers, via Mathlib's native monoid hom. -/
theorem pullback_pow (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (T : Over (Spec (.of O))) (f : T ⟶ A.X) (m : ℕ) :
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map (f ^ m) =
      ((Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map f) ^ m :=
  map_pow (Functor.homMonoidHom
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s))) f m

/-- Base change preserves pointwise inverses on the very same transported group object. -/
theorem pullback_inv (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (T : Over (Spec (.of O))) (f : T ⟶ A.X) :
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map f⁻¹ =
      ((Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map f)⁻¹ :=
  Functor.map_inv' _ f

/-- Integer powers are also transported by the native map on the group-valued Hom sets. -/
theorem pullback_zpow (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (T : Over (Spec (.of O))) (f : T ⟶ A.X) (n : ℤ) :
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map (f ^ n) =
      ((Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map f) ^ n :=
  (Functor.homMonoidHom
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s))).map_zpow f n

/-- The actual pullback of `[m]` is `[m]` on the SAME `mapGrp.obj` object. -/
theorem pullback_mul_id (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O)) (m : ℕ) :
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map
      (𝟙 A.X ^ m : A.X ⟶ A.X) =
        (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X) := by
  rw [pullback_pow A s A.X (𝟙 A.X) m, pullback_id A s]
  rfl

/-- Underlying scheme-map form of the actual fibre multiplication equality. -/
theorem pullback_mul_id_left (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (m : ℕ) :
    ((Over.pullback ((Spec (.of O)).fromSpecResidueField s)).map
      (𝟙 A.X ^ m : A.X ⟶ A.X)).left =
        (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left :=
  congrArg (fun f : (fibreGrp A s).X ⟶ (fibreGrp A s).X => f.left)
    (pullback_mul_id A s m)

/-- Explicit pullback-lift formula for the multiplication map, with no square hypothesis. -/
theorem fibre_mul_eq_lift (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (m : ℕ) :
    (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left =
      pullback.lift
        (A.X.hom.fiberι s ≫ (𝟙 A.X ^ m : A.X ⟶ A.X).left)
        (A.X.hom.fiberToSpecResidueField s)
        (by
          rw [Category.assoc, Over.w]
          exact A.X.hom.fiber_fac s) := by
  rw [← pullback_mul_id_left A s m]
  rfl

/-- The fibre inclusion intertwines the actual two multiplication maps. -/
@[reassoc]
theorem fibre_mul_fiberι (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (m : ℕ) :
    (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left ≫
      A.X.hom.fiberι s =
        A.X.hom.fiberι s ≫ (𝟙 A.X ^ m : A.X ⟶ A.X).left := by
  rw [fibre_mul_eq_lift]
  exact pullback.lift_fst _ _ _

/-- The multiplication map is over the actual residue-field spectrum. -/
@[reassoc]
theorem fibre_mul_toSpec (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (m : ℕ) :
    (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left ≫
      A.X.hom.fiberToSpecResidueField s = A.X.hom.fiberToSpecResidueField s := by
  exact Over.w (𝟙 (fibreGrp A s).X ^ m)

/-- The only fibre-domain adjustment needed for `fiberHom`: transport the PROVED `Over.w`
identity of structure maps. This is an equality isomorphism, not a different fibre model. -/
def fibreMulDomainIso (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O)) (m : ℕ) :
    ((𝟙 A.X ^ m : A.X ⟶ A.X).left ≫ A.X.hom).fiber s ≅ (fibreGrp A s).X.left :=
  eqToIso (congrArg (fun f : A.X.left ⟶ Spec (.of O) => f.fiber s)
    (Over.w (𝟙 A.X ^ m : A.X ⟶ A.X)))

/-- Equality transport of the native fibre inclusion. -/
@[reassoc]
theorem fibre_eqToHom_fiberι {X : Scheme.{0}} {p q : X ⟶ Spec (.of O)}
    (h : p = q) (s : Spec (.of O)) :
    eqToHom (congrArg (fun f : X ⟶ Spec (.of O) => f.fiber s) h) ≫ q.fiberι s =
      p.fiberι s := by
  cases h
  simp

/-- Equality transport of the native fibre-to-residue-field projection. -/
@[reassoc]
theorem fibre_eqToHom_toSpec {X : Scheme.{0}} {p q : X ⟶ Spec (.of O)}
    (h : p = q) (s : Spec (.of O)) :
    eqToHom (congrArg (fun f : X ⟶ Spec (.of O) => f.fiber s) h) ≫
      q.fiberToSpecResidueField s = p.fiberToSpecResidueField s := by
  cases h
  simp

/-- The forward domain adjustment preserves the native inclusion, by the actual `Over.w`. -/
@[reassoc]
theorem fibreMulDomainIso_hom_fiberι (A : Grp (Over (Spec (.of O))))
    (s : Spec (.of O)) (m : ℕ) :
    (fibreMulDomainIso A s m).hom ≫ A.X.hom.fiberι s =
      ((𝟙 A.X ^ m : A.X ⟶ A.X).left ≫ A.X.hom).fiberι s :=
  fibre_eqToHom_fiberι (Over.w (𝟙 A.X ^ m : A.X ⟶ A.X)) s

/-- The forward domain adjustment preserves the actual residue-field projection. -/
@[reassoc]
theorem fibreMulDomainIso_hom_toSpec (A : Grp (Over (Spec (.of O))))
    (s : Spec (.of O)) (m : ℕ) :
    (fibreMulDomainIso A s m).hom ≫ A.X.hom.fiberToSpecResidueField s =
      ((𝟙 A.X ^ m : A.X ⟶ A.X).left ≫ A.X.hom).fiberToSpecResidueField s :=
  fibre_eqToHom_toSpec (Over.w (𝟙 A.X ^ m : A.X ⟶ A.X)) s

/-- On every test object, the actual fibre multiplication acts by pointwise power. -/
theorem fibre_mul_on_points (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (T : Over (Spec ((Spec (.of O)).residueField s)))
    (x : T ⟶ (fibreGrp A s).X) (m : ℕ) :
    x ≫ (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X) = x ^ m := by
  rw [MonObj.comp_pow, Category.comp_id]

/-- The natural-power map agrees with the integer-power form used by field theorems. -/
theorem fibre_natPow_eq_zpow (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O))
    (m : ℕ) :
    (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X) =
      (𝟙 (fibreGrp A s).X ^ (m : ℤ) : (fibreGrp A s).X ⟶ (fibreGrp A s).X) := by
  rw [zpow_natCast]

/-- Canonical scalar map `O → κ(s)`, whose codomain is the actual scheme residue field. -/
def residueScalar (s : Spec (.of O)) : O →+* (Spec (.of O)).residueField s :=
  ((Scheme.ΓSpecIso (.of O)).inv ≫ (Spec (.of O)).Γevaluation s).hom

/-- This scalar map induces precisely the canonical point morphism used in `fibreGrp`. -/
theorem specMap_residueScalar (s : Spec (.of O)) :
    Spec.map (CommRingCat.ofHom (residueScalar s)) =
      (Spec (.of O)).fromSpecResidueField s := by
  letI := s.isPrime
  change Spec.map ((Scheme.ΓSpecIso (.of O)).inv ≫
    (Spec (.of O)).Γevaluation s) = _
  rw [show (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec (.of O)).Γevaluation s =
      CommRingCat.ofHom (algebraMap O s.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of O) s).inv from
      (Scheme.Spec.algebraMap_residueFieldIso_inv (.of O) s).symm]
  rw [Spec.map_comp]
  exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of O) s

/-- A unit natural number on the arbitrary base remains a unit in this actual `κ(s)`. -/
theorem isUnit_residue_natCast (s : Spec (.of O)) (m : ℕ) (hm : IsUnit (m : O)) :
    IsUnit (m : (Spec (.of O)).residueField s) := by
  simpa only [map_natCast] using hm.map (residueScalar s)

/-- Unit transport in the integer-cast form required by integer-multiplication field lemmas. -/
theorem isUnit_residue_intCast_nat (s : Spec (.of O)) (m : ℕ) (hm : IsUnit (m : O)) :
    IsUnit ((m : ℤ) : (Spec (.of O)).residueField s) := by
  simpa only [Int.cast_natCast] using isUnit_residue_natCast s m hm

/-- At an actual base point, an invertible natural scalar cannot be zero in the residue field. -/
theorem residue_natCast_ne_zero (s : Spec (.of O)) (m : ℕ) (hm : IsUnit (m : O)) :
    (m : (Spec (.of O)).residueField s) ≠ 0 :=
  (isUnit_residue_natCast s m hm).ne_zero

/-- The zero-unit case has no base points, without assuming the base ring is nontrivial. -/
theorem isEmpty_base_of_isUnit_zero (h0 : IsUnit (0 : O)) : IsEmpty (Spec (.of O)) := by
  refine ⟨fun s => ?_⟩
  have hres : IsUnit (0 : (Spec (.of O)).residueField s) := by
    simpa only [map_zero] using h0.map (residueScalar s)
  exact hres.ne_zero rfl

section Geometry

variable (A : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme A]

/-- Properness of the exact base-changed object, using the current `PkgI2` field. -/
theorem fibre_isProper (s : Spec (.of O)) : IsProper (fibreGrp A s).X.hom := by
  letI : IsProper A.X.hom := PkgI2.IsAbelianScheme.proper
  change IsProper (pullback.snd A.X.hom ((Spec (.of O)).fromSpecResidueField s))
  infer_instance

/-- Smoothness of the exact base-changed object. -/
theorem fibre_smooth (s : Spec (.of O)) : Smooth (fibreGrp A s).X.hom := by
  letI : Smooth A.X.hom := PkgI2.IsAbelianScheme.smooth
  change Smooth (pullback.snd A.X.hom ((Spec (.of O)).fromSpecResidueField s))
  infer_instance

/-- Geometrical connectedness of the exact base-changed object. -/
theorem fibre_geometricallyConnected (s : Spec (.of O)) :
    GeometricallyConnected (fibreGrp A s).X.hom := by
  letI : GeometricallyConnected A.X.hom := PkgI2.IsAbelianScheme.geomConnected
  change GeometricallyConnected
    (pullback.snd A.X.hom ((Spec (.of O)).fromSpecResidueField s))
  infer_instance

/-- The known smooth/connected bridge gives geometrical integrality on the SAME fibre. -/
theorem fibre_geometricallyIntegral (s : Spec (.of O)) :
    GeometricallyIntegral (fibreGrp A s).X.hom := by
  letI : IsProper (fibreGrp A s).X.hom := fibre_isProper A s
  exact FrobPieces.smoothGeomConnIntegral
    ((Spec (.of O)).residueField s) (fibreGrp A s).X.left (fibreGrp A s).X.hom
    (fibre_smooth A s) (fibre_geometricallyConnected A s) inferInstance

/-- The current native abelian-variety class is inhabited by the actual residue fibre. -/
theorem fibre_isAbelianVariety (s : Spec (.of O)) :
    PkgI2.IsAbelianVariety (fibreGrp A s) where
  proper := fibre_isProper A s
  smooth := fibre_smooth A s
  geomIntegral := fibre_geometricallyIntegral A s

end Geometry

end ZInQ.Contrib.MulEtale.FibreMaps
