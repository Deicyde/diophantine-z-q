import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.SliceTrivialization

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {S X Y Q : Scheme.{0}}

/-- Pullback of a unit automorphism, using the monoidal unit comparison. -/
def pullUnitIso (f : Y ⟶ X) (u : unit X ≅ unit X) : unit Y ≅ unit Y :=
  (pOU f).symm ≪≫ (pullback f).mapIso u ≪≫ pOU f

theorem pullUnitIso_coeff (f : Y ⟶ X) (u : unit X ≅ unit X) :
    unitHomAddEquiv (unit Y) (pullUnitIso f u).hom =
      f.appTop (unitHomAddEquiv (unit X) u.hom) :=
  pOU_conj f u.hom

@[simp] theorem pullUnitIso_id (u : unit X ≅ unit X) :
    pullUnitIso (𝟙 X) u = u := by
  apply Iso.ext
  apply (unitHomAddEquiv (unit X)).injective
  rw [pullUnitIso_coeff, Scheme.Hom.id_appTop]
  rfl

@[simp] theorem pullUnitIso_refl (f : Y ⟶ X) :
    pullUnitIso f (Iso.refl _) = Iso.refl _ := by simp [pullUnitIso]

theorem pullUnitIso_comp (g : S ⟶ Y) (f : Y ⟶ X) (u : unit X ≅ unit X) :
    pullUnitIso g (pullUnitIso f u) = pullUnitIso (g ≫ f) u := by
  apply Iso.ext
  apply (unitHomAddEquiv (unit S)).injective
  rw [pullUnitIso_coeff, pullUnitIso_coeff, pullUnitIso_coeff, Scheme.Hom.comp_appTop]
  rfl

theorem pullUnitIso_trans (f : Y ⟶ X) (u v : unit X ≅ unit X) :
    pullUnitIso f (u ≪≫ v) = pullUnitIso f u ≪≫ pullUnitIso f v := by
  apply Iso.ext
  simp [pullUnitIso]

theorem pullUnitIso_symm (f : Y ⟶ X) (u : unit X ≅ unit X) :
    pullUnitIso f u.symm = (pullUnitIso f u).symm := by
  apply Iso.ext
  simp [pullUnitIso]

theorem pullFrame_unitIso (f : Y ⟶ X) (u : unit X ≅ unit X) {M : X.Modules}
    (α : unit X ≅ M) :
    pullFrame f (u ≪≫ α) = pullUnitIso f u ≪≫ pullFrame f α := by
  apply Iso.ext
  simp [pullFrame, pullUnitIso]

/-- Two compatible prescribed frames on the coordinate sections of a product
extend to a common frame of a trivial line bundle on the product. -/
theorem exists_frame_matching_axes
    {M : Y.Modules} (α : unit Y ≅ M)
    (p : Y ⟶ X) (q : Y ⟶ Q) (s : X ⟶ Y) (t : Q ⟶ Y)
    (b : X ⟶ S) (c : Q ⟶ S) (x : S ⟶ X) (y : S ⟶ Q)
    (hsp : s ≫ p = 𝟙 X) (htq : t ≫ q = 𝟙 Q)
    (hsq : s ≫ q = b ≫ y) (htp : t ≫ p = c ≫ x)
    (hy : y ≫ c = 𝟙 S)
    (eX : unit X ≅ (pullback s).obj M) (eQ : unit Q ≅ (pullback t).obj M)
    (hOrigin : pullUnitIso x (eX ≪≫ (pullFrame s α).symm) =
      pullUnitIso y (eQ ≪≫ (pullFrame t α).symm)) :
    ∃ α' : unit Y ≅ M, pullFrame s α' = eX ∧ pullFrame t α' = eQ := by
  let u := eX ≪≫ (pullFrame s α).symm
  let v := eQ ≪≫ (pullFrame t α).symm
  let v' := v ≪≫ (pullUnitIso (t ≫ p) u).symm
  have hyv : pullUnitIso y v' = Iso.refl _ := by
    change pullUnitIso x u = pullUnitIso y v at hOrigin
    dsimp only [v']
    rw [pullUnitIso_trans, pullUnitIso_symm, pullUnitIso_comp, htp, ← Category.assoc, hy,
      Category.id_comp, hOrigin]
    simp
  refine ⟨pullUnitIso q v' ≪≫ pullUnitIso p u ≪≫ α, ?_, ?_⟩
  · simp only [pullFrame_unitIso, pullUnitIso_comp, hsp, pullUnitIso_id, hsq]
    rw [← pullUnitIso_comp b y, hyv, pullUnitIso_refl]
    apply Iso.ext
    simp [u]
  · simp only [pullFrame_unitIso, pullUnitIso_comp, htq, pullUnitIso_id]
    apply Iso.ext
    simp [v', v]

end PicDict.Transport

#print axioms PicDict.Transport.exists_frame_matching_axes
