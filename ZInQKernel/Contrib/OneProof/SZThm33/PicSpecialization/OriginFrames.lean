import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.TwoAxisFrames

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {S X P : Scheme.{0}}

/-- If all functions are pulled back from the base, every unit automorphism
is pulled back from its value at the section. -/
theorem pullUnitIso_origin_eq (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (hc : Function.Surjective f.appTop) (u : unit X ≅ unit X) :
    pullUnitIso f (pullUnitIso s u) = u := by
  apply Iso.ext
  apply (unitHomAddEquiv (unit X)).injective
  rw [pullUnitIso_coeff, pullUnitIso_coeff]
  let a : Γ(X, ⊤) := unitHomAddEquiv (unit X) u.hom
  change f.appTop (s.appTop a) = a
  obtain ⟨b, hb⟩ := hc a
  rw [← hb, ← CommRingCat.comp_apply f.appTop s.appTop, ← Scheme.Hom.comp_appTop, hs,
    Scheme.Hom.id_appTop]
  rfl

/-- A frame at the second axis can be rescaled over the base to match the
first-axis frame at their common origin. -/
theorem exists_frame_matching_origin
    (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (a b : X ⟶ P) (h : s ≫ b = s ≫ a) (M : P.Modules)
    (e : unit X ≅ (pullback a).obj M) (e' : unit X ≅ (pullback b).obj M) :
    ∃ d : unit X ≅ (pullback b).obj M,
      pullFrame s d ≪≫ (pullbackComp s b).app M ≪≫ (pullbackCongr h).app M =
        pullFrame s e ≪≫ (pullbackComp s a).app M := by
  let u := pullFrame s e ≪≫ (pullbackComp s a).app M
  let v := pullFrame s e' ≪≫ (pullbackComp s b).app M ≪≫ (pullbackCongr h).app M
  let w := u ≪≫ v.symm
  refine ⟨pullUnitIso f w ≪≫ e', ?_⟩
  rw [pullFrame_unitIso, pullUnitIso_comp, hs, pullUnitIso_id]
  apply Iso.ext
  simp only [w, u, v, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

end PicDict.Transport

#print axioms PicDict.Transport.exists_frame_matching_origin
