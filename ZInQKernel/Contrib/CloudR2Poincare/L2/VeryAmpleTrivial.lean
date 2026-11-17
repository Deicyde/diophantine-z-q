import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmpleSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.GlobalSections.Proper

/-!
# A trivial very ample line bundle forces a proper integral scheme to be finite

The proof uses only native global functions and projective coordinates. It does
not assume tensor-ampleness or an Euler-characteristic positivity statement.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open Scheme.Modules ProjectiveSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- On a proper integral scheme, a trivial very ample bundle makes the entire
scheme one affine projective-coordinate open. -/
theorem isAffine_of_veryAmple_of_trivial {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [IsIntegral X]
    (M : X.Modules) (hM : VeryAmple p M) (htriv : Nonempty (M ≅ unit X)) : IsAffine X := by
  classical
  obtain ⟨coordinates, hfinite, e, he, hp, ⟨comparison⟩⟩ := hM
  letI : IsClosedImmersion e := he
  obtain ⟨trivialization⟩ := htriv
  let N := twistRestrict e 1
  let κ : N ≅ unit X := comparison.symm ≪≫ trivialization
  let U : coordinates → X.Opens := fun i => e ⁻¹ᵁ standardOpen coordinates (Spec (.of k)) i
  letI : IsIso (homOfLE (le_top : e ⁻¹ᵁ ⊤ ≤ ⊤)) :=
    ⟨⟨homOfLE e.preimage_top.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  let restriction := (unit X).presheaf.map (homOfLE (le_top : e ⁻¹ᵁ ⊤ ≤ ⊤)).op
  haveI : IsIso restriction := inferInstance
  have hsurj := (ConcreteCategory.bijective_of_isIso restriction).2
  have globalCoordinates : ∀ i : coordinates, ∃ ci : Γ(X, ⊤), restriction ci =
      κ.hom.app (e ⁻¹ᵁ ⊤) (pullbackSection e
        (twistOneSection coordinates (Spec (.of k)) i)) :=
    fun i => hsurj _
  choose c hc using globalCoordinates
  have hκ (i : coordinates) : κ.hom.app _ (pullbackSection e
      (twistOneSection coordinates (Spec (.of k)) i)) =
      (unit X).presheaf.map (homOfLE (le_top : e ⁻¹ᵁ ⊤ ≤ ⊤)).op (c i) :=
    (hc i).symm
  have hgen (i : coordinates) : IsFreeGenerator
      ((unit X).presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (c i)) :=
    isFreeGenerator_of_twistRestrict_iso κ.hom hκ i
  have hcov : ⨆ i, U i = ⊤ := e.iSup_preimage_eq_top (iSup_standardOpen _ _)
  letI : Field Γ(X, ⊤) := (isField_of_universallyClosed k p).toField
  have hnonzero (i : coordinates) (x : X) (hx : x ∈ U i) : c i ≠ 0 := by
    intro hci
    exact freeGenerator_ne_zero (U i) ⟨x, hx⟩ _ (hgen i) (by rw [hci, map_zero])
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial))
  have hci : IsUnit (c i) := isUnit_iff_ne_zero.mpr (hnonzero i x hi)
  have htop : U i = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcov.symm ▸ (show y ∈ (⊤ : X.Opens) from trivial))
    have hcj : IsUnit (c j) := isUnit_iff_ne_zero.mpr (hnonzero j y hj)
    let ci := X.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (c i)
    let cj := X.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (c j)
    let r := e.app (standardOpen coordinates (Spec (.of k)) j)
      (coordRatio coordinates (Spec (.of k)) j i)
    have hrel : ci = r * cj := by
      exact map_eq_coordRatio_smul_of_twistRestrict_iso κ.hom hκ j i
    have hci' : IsUnit ci := (X.presheaf.map (homOfLE le_top).op).hom.isUnit_map hci
    have hcj' : IsUnit cj := (X.presheaf.map (homOfLE le_top).op).hom.isUnit_map hcj
    obtain ⟨ui, hui⟩ := hci'
    have hmul : r * cj = (ui : Γ(X, U j)) := hrel.symm.trans hui.symm
    have hr : IsUnit r := IsUnit.of_mul_eq_one (cj * ↑ui⁻¹) (by
      rw [← mul_assoc, hmul]
      exact Units.mul_inv ui)
    have hbo : X.basicOpen r = U j := X.basicOpen_of_isUnit hr
    have hbasic : X.basicOpen r = U j ⊓ U i := by
      dsimp [r]
      rw [← Scheme.preimage_basicOpen, basicOpen_coordRatio, Scheme.Hom.preimage_inf]
    have hy : y ∈ U j ⊓ U i := hbasic ▸ (hbo.symm ▸ hj)
    exact hy.2
  have haff : IsAffineOpen (U i) := (isAffineOpen_standardOpen coordinates (Spec (.of k)) i).preimage e
  rw [htop] at haff
  haveI : IsAffine (⊤ : X.Opens).toScheme := haff
  exact IsAffine.of_isIso X.topIso.inv

/-- A proper integral scheme with a trivial very ample bundle is finite over
its original field. -/
theorem isFinite_of_veryAmple_of_trivial {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [IsIntegral X]
    (M : X.Modules) (hM : VeryAmple p M) (htriv : Nonempty (M ≅ unit X)) : IsFinite p := by
  letI : IsAffine X := isAffine_of_veryAmple_of_trivial p M hM htriv
  exact (IsFinite.iff_isProper_and_isAffineHom).mpr ⟨inferInstance, inferInstance⟩

/-- In particular the dimension is at most zero; this is the contradiction
with a positive-dimensional abelian subvariety. -/
theorem dimension_le_zero_of_veryAmple_of_trivial {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [IsIntegral X]
    (M : X.Modules) (hM : VeryAmple p M) (htriv : Nonempty (M ≅ unit X)) :
    topologicalKrullDim X ≤ 0 := by
  letI : IsFinite p := isFinite_of_veryAmple_of_trivial p M hM htriv
  letI : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite p
  exact topologicalKrullDim_zero_of_discreteTopology X

end ZInQ.Contrib.CloudR2Poincare.L2
