import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.AxisFrameRestriction

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {S X Y Q : Scheme.{0}}

private theorem pullFrame_congr {f g : S ⟶ Y} (he : f = g) {M : Y.Modules} (α : unit Y ≅ M) :
    pullFrame f α ≪≫ (pullbackCongr he).app M = pullFrame g α := by
  subst he
  apply Iso.ext
  simp [pullbackCongr]

private theorem pullUnitIso_ratio (a : S ⟶ X) (s : X ⟶ Y)
    {M : Y.Modules} (e d : unit X ≅ (pullback s).obj M) :
    pullUnitIso a (e ≪≫ d.symm) ≪≫ pullFramedAlong a s d = pullFramedAlong a s e := by
  rw [pullFramedAlong, pullFramedAlong, ← Iso.trans_assoc, ← pullFrame_unitIso]
  apply Iso.ext
  simp

/-- A trivial product line can be framed compatibly with two axis frames
which agree at the common origin. -/
theorem exists_frame_matching_axes_of_origin
    {M : Y.Modules} (α : unit Y ≅ M)
    (p : Y ⟶ X) (q : Y ⟶ Q) (s : X ⟶ Y) (t : Q ⟶ Y)
    (b : X ⟶ S) (c : Q ⟶ S) (x : S ⟶ X) (y : S ⟶ Q)
    (hsp : s ≫ p = 𝟙 X) (htq : t ≫ q = 𝟙 Q)
    (hsq : s ≫ q = b ≫ y) (htp : t ≫ p = c ≫ x)
    (hy : y ≫ c = 𝟙 S) (hOrigins : x ≫ s = y ≫ t)
    (eX : unit X ≅ (pullback s).obj M) (eQ : unit Q ≅ (pullback t).obj M)
    (hFrame : pullFramedAlong x s eX ≪≫ (pullbackCongr hOrigins).app M =
      pullFramedAlong y t eQ) :
    ∃ α' : unit Y ≅ M, pullFrame s α' = eX ∧ pullFrame t α' = eQ := by
  apply exists_frame_matching_axes α p q s t b c x y hsp htq hsq htp hy eX eQ
  have hOld : pullFramedAlong x s (pullFrame s α) ≪≫ (pullbackCongr hOrigins).app M =
      pullFramedAlong y t (pullFrame t α) := by
    simp only [pullFramedAlong, pullFrame_comp]
    exact pullFrame_congr hOrigins α
  have hc : pullUnitIso x (eX ≪≫ (pullFrame s α).symm) ≪≫ pullFramedAlong y t (pullFrame t α) =
      pullUnitIso y (eQ ≪≫ (pullFrame t α).symm) ≪≫ pullFramedAlong y t (pullFrame t α) := by
    conv_lhs =>
      rw [← hOld, ← Iso.trans_assoc, pullUnitIso_ratio, hFrame]
    rw [pullUnitIso_ratio]
  apply Iso.ext
  rw [← cancel_mono (pullFramedAlong y t (pullFrame t α)).hom]
  exact congrArg Iso.hom hc

end PicDict.Transport

#print axioms PicDict.Transport.exists_frame_matching_axes_of_origin
