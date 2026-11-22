import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricEvaluation

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y P Z : Scheme.{0}}

private theorem pullFrame_composite_congr {u v : Z ⟶ Y} (huv : u = v) (i : Y ⟶ P)
    (w : Z ⟶ P) (M : P.Modules) (α : unit Y ≅ (pullback i).obj M)
    (hu : u ≫ i = w) (hv : v ≫ i = w) :
    pullFrame u α ≪≫ (pullbackComp u i).app M ≪≫ (pullbackCongr hu).app M =
      pullFrame v α ≪≫ (pullbackComp v i).app M ≪≫ (pullbackCongr hv).app M := by
  subst huv
  rfl

/-- If a translated test point and the original test point factor through
a framed subscheme, have identical multiplied images in that subscheme, and
give the same comparison scalar, the Mumford coefficient at that test
point is one. The two axis frames identify its right multiplication frames. -/
theorem wf_eval_eq_one_of_framed_comparison
    (g : Z ⟶ X) (t m : X ⟶ X) (ht : t ≫ m = m)
    (x₀ x₁ : Z ⟶ Y) (i : Y ⟶ P) (a b : X ⟶ P) (l r : P ⟶ P)
    (hm : m ≫ a = a ≫ l) (hb : a ≫ r = b)
    (hx₀ : x₀ ≫ i = g ≫ a) (hx₁ : x₁ ≫ i = (g ≫ t) ≫ a)
    (ml mr : Y ⟶ Y) (hl : i ≫ l = ml ≫ i) (hr : i ≫ r = mr ≫ i)
    (M : P.Modules) (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) (e : unit X ≅ (pullback b).obj M)
    (he₀ : pullFrame g e ≪≫ (pullbackComp g b).app M ≪≫
      (pullbackCongr (show g ≫ b = (x₀ ≫ i) ≫ r by rw [hx₀, Category.assoc, hb])).app M =
        evalFrameOnComposite x₀ i mr r hr M α)
    (he₁ : pullFrame (g ≫ t) e ≪≫ (pullbackComp (g ≫ t) b).app M ≪≫
      (pullbackCongr (show (g ≫ t) ≫ b = (x₁ ≫ i) ≫ r by simp only [hx₁, Category.assoc, hb])).app M =
        evalFrameOnComposite x₁ i mr r hr M α)
    (hpoint : x₁ ≫ ml = x₀ ≫ ml)
    (hscalar :
      pullUnitIso x₁ (comparisonDefect i ml mr l r hl hr M J α) =
        pullUnitIso x₀ (comparisonDefect i ml mr l r hl hr M J α)) :
    g.appTop (wf t m ht ((pullback a).obj M)
      (sliceComparisonTriv m a b l r hm hb M J e)) = 1 := by
  let ψ := sliceComparisonTriv m a b l r hm hb M J e
  have h₀ := evalTriv_sliceComparison_on_framed_subscheme g x₀ i m a b l r hm hb hx₀
    ml mr hl hr M J α e he₀
  have h₁ := evalTriv_sliceComparison_on_framed_subscheme (g ≫ t) x₁ i m a b l r hm hb hx₁
    ml mr hl hr M J α e he₁
  let hmul : (g ≫ t) ≫ m = g ≫ m := by rw [Category.assoc, ht]
  let htarget : ((g ≫ t) ≫ m) ≫ a = (g ≫ m) ≫ a := congrArg (· ≫ a) hmul
  have hc : (evalTriv (g ≫ t) m ((pullback a).obj M) ψ ≪≫
        (pullbackComp ((g ≫ t) ≫ m) a).app M) ≪≫ (pullbackCongr htarget).app M =
      evalTriv g m ((pullback a).obj M) ψ ≪≫ (pullbackComp (g ≫ m) a).app M := by
    dsimp only [ψ]
    rw [h₀, h₁, hscalar, evalFrameOnComposite_eq, evalFrameOnComposite_eq]
    have hs := pullFrame_composite_congr hpoint i ((g ≫ m) ≫ a) M α (by
      calc
        (x₁ ≫ ml) ≫ i = (x₁ ≫ i) ≫ l := by simp only [Category.assoc, hl]
        _ = ((g ≫ t) ≫ m) ≫ a := by simp only [hx₁, Category.assoc, hm]
        _ = (g ≫ m) ≫ a := htarget) (by
      calc
        (x₀ ≫ ml) ≫ i = (x₀ ≫ i) ≫ l := by simp only [Category.assoc, hl]
        _ = (g ≫ m) ≫ a := by rw [hx₀, Category.assoc, Category.assoc, hm])
    apply Iso.ext
    have hs' := congrArg Iso.hom hs
    simp only [Iso.trans_hom, Category.assoc, Iso.app_hom, pullbackCongr_hom_app] at hs' ⊢
    simp only [eqToHom_trans, hs']
  have he : evalTriv (g ≫ t) m ((pullback a).obj M) ψ ≪≫
      (pullbackCongr hmul).app ((pullback a).obj M) =
      evalTriv g m ((pullback a).obj M) ψ := by
    apply Iso.ext
    rw [← cancel_mono ((pullbackComp (g ≫ m) a).hom.app M)]
    have hc' := congrArg Iso.hom hc
    simp only [Iso.trans_hom, Category.assoc, Iso.app_hom, pullbackCongr_hom_app] at hc' ⊢
    rw [eqToHom_comp_pullbackComp hmul a M]
    exact hc'
  rw [wf_eval]
  change unitHomAddEquiv (unit Z) (evalTrivRatio g t m ht ((pullback a).obj M) ψ).hom = (1 : Γ(Z, ⊤))
  rw [evalTrivRatio, ← Iso.trans_assoc, he]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id]
  rfl

end PicDict.Transport

#print axioms PicDict.Transport.wf_eval_eq_one_of_framed_comparison
