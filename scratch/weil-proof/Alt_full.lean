import ZInQKernel.Contrib.OneProof.WeilFormulaTheta

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace WeilProof.Theta

open PicDict PkgI3 PkgI3.AbVar MonoidalCategory Scheme.Modules PicDict.Transport
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k]

/-- **Mumford §23 from divisibility.** -/
theorem mumfordWeilAltAC_of_div (hdiv : DivisibleAC) : MumfordWeilAltAC := by
  intro k _ _ X n hn hnk c₀ x hx ψ
  obtain ⟨y, rfl⟩ := hdiv k X n hn hnk x
  set m := (AC.mul X n).left with hm
  set t := (AC.tr (y ^ n)).left with ht_def
  set s := (AC.tr y).left with hs_def
  have h : t ≫ m = m := by rw [← Over.comp_left, AC.tr_comp_mul _ hx]
  have hb : m ≫ t = s ≫ m := by rw [← Over.comp_left, ← Over.comp_left, tr_mul_comm]
  have hab : t ≫ s = s ≫ t := by
    rw [← Over.comp_left, ← Over.comp_left, AC.tr_comp_tr, AC.tr_comp_tr, mul_comm]
  have ht : ∀ r : Γ(X.X.left, ⊤), t.appTop r = r := tr_appTop X _
  have hs : ∀ r : Γ(X.X.left, ⊤), s.appTop r = r := tr_appTop X y
  set L := AC.modX c₀ with hL
  set N := (Scheme.Modules.pullback m).obj L with hN
  set Φ := AC.modX (AC.phi c₀ (y ^ n)) with hΦ
  -- the unit constraint of `t^*`
  have hr : (pOU t).inv = Functor.LaxMonoidal.ε (Scheme.Modules.pullback t) := by
    have h1 := unitRatio_tr pullbackCompMonoidal_proof X (y ^ n) hx
    have h2 : unitRatio t = 𝟙 _ := (unitHomAddEquiv (unit X.X.left)).injective (h1.trans id_val.symm)
    have h3 := congrArg (· ≫ Functor.LaxMonoidal.ε (Scheme.Modules.pullback t)) h2
    simp only [unitRatio, Category.assoc, Category.id_comp] at h3
    rw [← Functor.Monoidal.εIso_hom, Iso.inv_hom_id] at h3
    exact (Category.comp_id _).symm.trans h3
  -- `Φ ⊗ L ≅ t^* L`
  have hcl : AC.phi c₀ (y ^ n) * c₀ = Scheme.Pic.map t c₀ := by
    simp only [AC.phi, inv_mul_cancel_right]
    rfl
  let w : Φ ⊗ L ≅ (Scheme.Modules.pullback t).obj L :=
    (Scheme.Pic.mulIso _ _).symm ≪≫ eqToIso (congrArg (fun c => (fromSkeleton _).obj c.val) hcl) ≪≫
      Scheme.Pic.mkIso _
  let u : N ⟶ (Scheme.Modules.pullback m).obj (Φ ⊗ L) :=
    (λ_ N).inv ≫ (ψ.hom ▷ N) ≫ Functor.LaxMonoidal.μ (Scheme.Modules.pullback m) Φ L
  let β : N ⟶ (Scheme.Modules.pullback s).obj N :=
    u ≫ (Scheme.Modules.pullback m).map w.hom ≫ rhoAB hb L
  let A := alpha t m h Φ ψ
  let EA : N ⟶ N := (λ_ N).inv ≫ (A ▷ N) ≫ (λ_ N).hom
  have R : (Scheme.Modules.pullback t).map β ≫ swapAB hab N ≫ (Scheme.Modules.pullback s).map (thetaT h L) =
      thetaT h L ≫ EA ≫ β := by
    have trel := tensor_relation pullbackCompMonoidal_proof h hr Φ L ψ
    have nat : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback m).map w.hom) ≫
        thetaT h ((Scheme.Modules.pullback t).obj L) = thetaT h (Φ ⊗ L) ≫ (Scheme.Modules.pullback m).map w.hom := by
      have n1 := (pullbackComp t m).hom.naturality w.hom
      have n2 := (pullbackCongr h).hom.naturality w.hom
      simp only [Functor.comp_map] at n1 n2
      simp only [thetaT, ← Category.assoc, n1]
      simp only [Category.assoc, n2]
    have tro : thetaT h ((Scheme.Modules.pullback t).obj L) ≫ rhoAB hb L =
        (Scheme.Modules.pullback t).map (rhoAB hb L) ≫ swapAB hab N ≫
          (Scheme.Modules.pullback s).map (thetaT h L) := theta_rho h hb hab L
    simp only [β, u, EA, Functor.map_comp, Category.assoc]
    rw [← tro, reassoc_of% nat]
    sorry
  sorry

end WeilProof.Theta
