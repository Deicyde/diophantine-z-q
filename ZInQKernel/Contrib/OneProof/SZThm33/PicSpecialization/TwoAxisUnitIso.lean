import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.TwoAxisFrames
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.AffineLineUnitRigidity

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X : Scheme.{0}}

/-- The global scalar of an endomorphism of the unit sheaf. -/
abbrev unitCoeff (f : unit X ⟶ unit X) : Γ(X, ⊤) :=
  unitHomAddEquiv (unit X) f

theorem unitCoeff_comp (f g : unit X ⟶ unit X) :
    unitCoeff (f ≫ g) = unitCoeff f * unitCoeff g := by
  let a : Γ(X, ⊤) := unitHomAddEquiv (unit X) f
  let b : Γ(X, ⊤) := unitHomAddEquiv (unit X) g
  change g.app ⊤ a = a * b
  have hg : homOfGlobalSection (unit X) b = g :=
    (unitHomAddEquiv (unit X)).symm_apply_apply g
  rw [← hg]
  have e := homOfGlobalSection_app (unit X) b (⊤ : X.Opens) a
  rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 ⊤ from rfl,
    op_id, (unit X).presheaf.map_id] at e
  exact e

/-- Automorphisms of the unit sheaf give units in the ring of global functions. -/
def coeffUnit (e : unit X ≅ unit X) : Γ(X, ⊤)ˣ where
  val := unitCoeff e.hom
  inv := unitCoeff e.inv
  val_inv := by rw [← unitCoeff_comp, e.hom_inv_id]; rfl
  inv_val := by rw [← unitCoeff_comp, e.inv_hom_id]; rfl

end PicDict.Transport

namespace ZInQ.ToricOrthogonality

open PicDict.Transport

private theorem ratio_eq_one_on_section {X Z : Scheme.{0}} (i : Z ⟶ X)
    (u v : unit X ≅ unit X) (hi : pullUnitIso i u = pullUnitIso i v) :
    i.appTop (coeffUnit (u ≪≫ v.symm)).val = 1 := by
  change i.appTop (unitHomAddEquiv (unit X) (u ≪≫ v.symm).hom) = 1
  rw [← pullUnitIso_coeff]
  simp only [pullUnitIso_trans, pullUnitIso_symm, hi, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id]
  rfl

private theorem unitIso_eq_of_ratio_one {X : Scheme.{0}} (u v : unit X ≅ unit X)
    (h : (coeffUnit (u ≪≫ v.symm)).val = 1) : u = v := by
  have h' : u ≪≫ v.symm = Iso.refl _ := by
    apply Iso.ext
    apply (unitHomAddEquiv (unit X)).injective
    exact h
  apply Iso.ext
  have e := congrArg (fun z : unit X ≅ unit X => (z ≪≫ v).hom) h'
  simpa using e

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) {h : Polynomial k}

/-- Two unit automorphisms agreeing on the two coordinate sections agree
on the product with an open affine line. -/
theorem unitIso_eq_of_coordinate_sections (hh : h ≠ 0) [IsIntegral (Limits.pullback f (affineLineOpenMap h))]
    {s : X ⟶ Limits.pullback f (affineLineOpenMap h)}
    (hs : s ≫ pullback.fst f (affineLineOpenMap h) = 𝟙 X)
    {a : Spec (.of k) ⟶ Spec (.of (Localization.Away h))}
    (hsa : s ≫ pullback.snd f (affineLineOpenMap h) = f ≫ a)
    {t : Spec (.of (Localization.Away h)) ⟶ Limits.pullback f (affineLineOpenMap h)}
    (ht : t ≫ pullback.snd f (affineLineOpenMap h) = 𝟙 (Spec (.of (Localization.Away h))))
    (u v : unit (Limits.pullback f (affineLineOpenMap h)) ≅ unit (Limits.pullback f (affineLineOpenMap h)))
    (hu : pullUnitIso s u = pullUnitIso s v) (hv : pullUnitIso t u = pullUnitIso t v) :
    u = v := by
  apply unitIso_eq_of_ratio_one
  exact unit_eq_one_of_coordinate_sections f hh hs hsa ht (coeffUnit (u ≪≫ v.symm))
    (ratio_eq_one_on_section s u v hu) (ratio_eq_one_on_section t u v hv)

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.unitIso_eq_of_coordinate_sections
