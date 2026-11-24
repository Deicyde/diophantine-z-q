import ZInQKernel.Contrib.OneProof.SZThm33.PullbackTate

/-!
# Pullback commutes with lifting residue Tate towers
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open IsLocalRing

namespace SmoothGroup

variable {S B R : Type} [CommRing S] [CommRing B] [CommRing R] [HenselianLocalRing R]
  (d : Spec (.of B) ⟶ Spec (.of S))
  (g : Spec (.of R) ⟶ Spec (.of B)) (g₀ : Spec (.of R) ⟶ Spec (.of S))
  (h : g ≫ d = g₀) (X : Over (Spec (.of S))) [GrpObj X] [IsCommMonObj X]
  [Smooth X.hom] {ℓ : ℕ} [Fact ℓ.Prime]
  (hu : IsUnit (ℓ : S)) (hu' : IsUnit (ℓ : B))

local instance : GrpObj (Functor.obj (Over.pullback d) X) := Functor.grpObjObj
local instance : IsCommMonObj (Functor.obj (Over.pullback d) X) := Functor.isCommMonObj_obj (F := Over.pullback d)
local instance : Smooth (Functor.obj (Over.pullback d) X).hom := inferInstanceAs (Smooth (pullback.snd X.hom d))

set_option maxHeartbeats 1200000 in
/-- The unique prime-to-residue torsion lift is compatible with changing the
base of the group model while the henselian test scheme stays the same. -/
theorem liftTateFromResidue_pullbackTestTate {T : Scheme} (a : T ⟶ Spec (.of R))
    (x : PkgI3.Tate.T ℓ (Additive (Over.mk ((Spec.map (CommRingCat.ofHom (residue R))) ≫ g₀) ⟶ X))) :
    liftTateFromResidue g hu' a
      (pullbackTestTate d ((Spec.map (CommRingCat.ofHom (residue R))) ≫ g) ((Spec.map (CommRingCat.ofHom (residue R))) ≫ g₀) (by rw [Category.assoc, h]) X x) =
      pullbackTestTate d (a ≫ g) (a ≫ g₀) (by rw [Category.assoc, h]) X
        (liftTateFromResidue g₀ hu a x) := by
  let e₀ := LinearEquiv.ofBijective _ (restrictTate_bijective_of_residue (X := X) (ℓ := ℓ) g₀ hu)
  let e₁ := LinearEquiv.ofBijective _ (restrictTate_bijective_of_residue (X := (Functor.obj (Over.pullback d) X)) (ℓ := ℓ) g hu')
  let qr := pullbackTestTate (ℓ := ℓ) d ((Spec.map (CommRingCat.ofHom (residue R))) ≫ g)
    ((Spec.map (CommRingCat.ofHom (residue R))) ≫ g₀) (by rw [Category.assoc, h]) X
  let qa := pullbackTestTate (ℓ := ℓ) d (a ≫ g) (a ≫ g₀) (by rw [Category.assoc, h]) X
  let q := pullbackTestTate (ℓ := ℓ) d g g₀ h X
  have h₁ : e₁.symm (qr x) = q (e₀.symm x) := by
    apply e₁.injective
    rw [LinearEquiv.apply_symm_apply]
    have hr := pullbackTestTate_restrict d g g₀ h X (Spec.map (CommRingCat.ofHom (residue R))) (e₀.symm x)
    change e₁ (q (e₀.symm x)) = qr (e₀ (e₀.symm x)) at hr
    exact (congrArg qr (e₀.apply_symm_apply x)).symm.trans hr.symm
  let src := restrictTate (ℓ := ℓ) (X := (Functor.obj (Over.pullback d) X)) (g := g) a
  let dst := restrictTate (ℓ := ℓ) (X := X) (g := g₀) a
  let t := e₀.symm x
  have e : src (e₁.symm (qr x)) = src (q t) := congrArg src h₁
  have en : src (q t) = qa (dst t) := pullbackTestTate_restrict d g g₀ h X a t
  unfold liftTateFromResidue
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact e.trans en

#print axioms liftTateFromResidue_pullbackTestTate

end SmoothGroup
