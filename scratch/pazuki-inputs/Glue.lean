import ZInQKernel.Contrib.OneProof.PazukiAlg

noncomputable section

namespace PazukiInputs

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open ZInQ.LeafPush2 (CPts)
open AvSplit.HomLatticeAN3 (bcC ptE)
open PazukiDict (OnZeroLocus IsSymmPrincipal liftPt specMap_comp_eq)
open PazukiAlg (pullbackSec support_zeroLocus_pullbackSec)

variable {K K' : Type} [Field K] [Field K'] [Algebra K K']

/-- The projection `A ×_{K,σ} ℂ → A ×_K K'` over `σ' : K' → ℂ` (on the fibre products). -/
def bcMap' (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ) :
    pullback A.X.hom (Spec.map (CommRingCat.ofHom σ)) ⟶
      pullback A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))) :=
  pullback.lift (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)))
    (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)) ≫ Spec.map (CommRingCat.ofHom σ')) (by
      have h := pullback.condition (f := A.X.hom) (g := Spec.map (CommRingCat.ofHom σ))
      exact h.trans ((congrArg (fun g => pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)) ≫ g)
        (specMap_comp_eq σ σ' hσ).symm).trans (Category.assoc _ _ _).symm))

/-- The projection `A_ℂ = A ×_{K,σ} ℂ → A_{K'} = A ×_K K'` over `σ' : K' → ℂ`. -/
def bcMap (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ) :
    (bcC A σ).X.left ⟶ (A.baseChange K').X.left :=
  bcMap' A σ σ' hσ

theorem liftPt_ptE (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) (p : CPts (bcC A σ) (RingHom.id ℂ)) :
    liftPt A σ σ' hσ (ptE A σ p) = p.left ≫ bcMap A σ σ' hσ := by
  apply pullback.hom_ext
  · unfold liftPt bcMap bcMap'
    erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, AvSplit.HomLatticeAN3.ptE_left]
    rfl
  · have h : p.left ≫ pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)) = 𝟙 _ := by
      have := Over.w p
      refine this.trans ?_
      change Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) = 𝟙 _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    unfold liftPt bcMap bcMap'
    erw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact ((congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom σ')) h).trans
      (Category.id_comp _)).symm.trans (Category.assoc _ _ _)

theorem bcMap_isPullback (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) :
    IsPullback (bcMap' A σ σ' hσ) (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ)))
      (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
      (Spec.map (CommRingCat.ofHom σ')) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (v₁₃ := A.X.hom) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap K K'))) ?_ ?_
    (IsPullback.of_hasPullback _ _)
  · rw [bcMap', pullback.lift_fst]
    have key : ∀ g' : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of K),
        g' = Spec.map (CommRingCat.ofHom σ) →
        IsPullback (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)))
          (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom σ))) A.X.hom g' := by
      rintro g' rfl
      exact IsPullback.of_hasPullback _ _
    exact key _ (specMap_comp_eq σ σ' hσ)
  · rw [bcMap', pullback.lift_snd]

instance (L : Type) [Field L] : Subsingleton (Spec (CommRingCat.of L)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum L))

theorem surjective_bcMap (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) : Surjective (bcMap A σ σ' hσ) := by
  have hs : Surjective (Spec.map (CommRingCat.ofHom σ')) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (P := @Surjective) (bcMap_isPullback A σ σ' hσ).flip hs

end PazukiInputs
