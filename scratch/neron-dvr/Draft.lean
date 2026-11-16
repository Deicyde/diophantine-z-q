import ZInQKernel.Contrib.OneProof.BLRLocalizes

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField

set_option linter.style.haveILetI false

namespace GapNeron

open ReductSplit

def NeronSchemeModelExistsDVRNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of O))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (e : (Over.pullback (jO O)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
        Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom

theorem neronSchemeModelExistsDVRNF_of_field (h : ReductSplit.NeronSchemeModelExistsDVR) :
    NeronSchemeModelExistsDVRNF :=
  fun K _ _ O _ A => h K O A

/-- `A_K ≅ A` for the base change along `id : K → K`. -/
noncomputable irreducible_def bcSelfIso {K : Type} [Field K] (A : PkgI3.AbVar K) : (A.baseChange K).X ≅ A.X :=
  eqToIso (by
    show (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K)))).obj A.X =
      (Over.pullback (𝟙 _)).obj A.X
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]) ≪≫ Over.pullbackId.app A.X

/-- Postcomposition with an isomorphism does not change bijectivity (any domain). -/
theorem bijective_comp_iso' {α : Type*} {C : Type*} [Category C] {Z W W' : C} (F : α → (Z ⟶ W))
    (e : W ≅ W') : Function.Bijective (fun f => F f ≫ e.hom) ↔ Function.Bijective F := by
  have : (fun f => F f ≫ e.hom) = (fun g : Z ⟶ W => g ≫ e.hom) ∘ F := rfl
  rw [this]
  have hb : Function.Bijective (fun g : Z ⟶ W => g ≫ e.hom) :=
    ⟨fun g₁ g₂ h => by simpa using congrArg (· ≫ e.inv) h,
      fun g => ⟨g ≫ e.inv, by simp⟩⟩
  exact ⟨fun h => (Function.Bijective.of_comp_iff' hb F).mp h, fun h => hb.comp h⟩

theorem bijective_trans {K : Type} [Field K] (O : ValuationSubring K) {B B' : PkgI3.AbVar K}
    (G : Over (Spec (CommRingCat.of O))) (g : (Over.pullback (jO O)).obj G ≅ B.X) (e : B.X ≅ B'.X)
    (Y : Over (Spec (CommRingCat.of O)))
    (hb : Function.Bijective fun f : Y ⟶ G => (Over.pullback (jO O)).map f ≫ g.hom) :
    Function.Bijective fun f : Y ⟶ G => (Over.pullback (jO O)).map f ≫ (g ≪≫ e).hom := by
  have h2 := (bijective_comp_iso' _ e).mpr hb
  simpa only [Iso.trans_hom, Category.assoc] using h2

theorem neronSchemeModelExistsNF (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) :
    NeronSchemeModelExistsDVRNF := by
  intro K _ _ O _ A
  obtain ⟨𝒩, h𝒩⟩ := ZInQ.Contrib.NeronC.neronModelExists_of_extension hN1 K A K
  have h := GapBLR.neronLocalizesDVR_proved K A K 𝒩 h𝒩 O
  exact ⟨(ReductGlue.toO 𝒩 O).G, inferInstance, inferInstance, inferInstance,
    (ReductGlue.toO 𝒩 O).gen ≪≫ bcSelfIso A,
    fun Y _ => bijective_trans O (ReductGlue.toO 𝒩 O).G _ (bcSelfIso A) Y (h Y)⟩

end GapNeron

#print axioms GapNeron.neronSchemeModelExistsNF
