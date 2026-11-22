import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricComparisonScalar
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricVanishing

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

open PicDict.Transport

variable {k : Type} [Field k] [IsAlgClosed k] {S : Scheme.{0}}
  (G : Over S) [GrpObj G] (H : Over (Spec (.of k))) [GrpObj H] [IsIntegral H.left]
  (j : Spec (.of k) ⟶ S) (p : H.left ⟶ G.left)
  (hp : p ≫ G.hom = H.hom ≫ j) (d : puncturedLine k ⟶ H) [IsMonHom d]
  (hη : η[H].left ≫ p = j ≫ η[G].left)

omit [IsAlgClosed k] [GrpObj G] [GrpObj H] [IsIntegral H.left] [IsMonHom d] in
private theorem point_comp_toricProductMap
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ puncturedLine k)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ H)
    {X : Scheme.{0}} (s : Spec (.of k) ⟶ X) (a : X ⟶ (G ⊗ G).left)
    (hf : s ≫ a ≫ (fst G G).left = x.left ≫ d.left ≫ p)
    (hs : s ≫ a ≫ (snd G G).left = y.left ≫ p) :
    (lift y x : 𝟙_ (Over (Spec (.of k))) ⟶ H ⊗ puncturedLine k).left ≫
      toricProductMap G H (puncturedLine k) j p hp d = s ≫ a := by
  have hx' : (lift y x).left ≫ (snd H (puncturedLine k)).left = x.left :=
    congrArg Over.Hom.left (lift_snd y x)
  have hy' : (lift y x).left ≫ (fst H (puncturedLine k)).left = y.left :=
    congrArg Over.Hom.left (lift_fst y x)
  apply modelProduct_hom_ext G
  · simp only [Category.assoc, toricProductMap_fst, reassoc_of% hx', hf]
  · simp only [Category.assoc, toricProductMap_snd, reassoc_of% hy', hs]

omit [IsAlgClosed k] [IsIntegral H.left] in
private theorem point_comp_groupDilation
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ puncturedLine k)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ H) (n : ℕ) (hy : y ^ n = 1) :
    lift y x ≫ groupDilation H (puncturedLine k) n = x ≫ torusAxis H (puncturedLine k) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, groupDilation, torusAxis, lift_fst, lift_snd,
      MonObj.comp_pow, MonObj.comp_one, Category.comp_id, hy]

omit [IsAlgClosed k] [GrpObj H] [IsIntegral H.left] in
private theorem points_comp_torusDilation_eq
    (x₀ x₁ : 𝟙_ (Over (Spec (.of k))) ⟶ puncturedLine k)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ H) (n : ℕ) (hx₀ : x₀ ^ n = 1) (hx₁ : x₁ ^ n = 1) :
    lift y x₁ ≫ torusDilation H (puncturedLine k) n =
      lift y x₀ ≫ torusDilation H (puncturedLine k) n := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, torusDilation, lift_fst, lift_snd, MonObj.comp_pow, hx₀, hx₁]

private theorem framedAlong_move {A B C : Scheme.{0}} {f g : A ⟶ B} (h : f = g)
    (i : B ⟶ C) (z : A ⟶ C) {M : C.Modules} (α : unit B ≅ (pullback i).obj M)
    (hf : f ≫ i = z) (hg : g ≫ i = z) :
    pullFramedAlong f i α ≪≫ (pullbackCongr hf).app M =
      pullFramedAlong g i α ≪≫ (pullbackCongr hg).app M := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
/-- The relative Weil coefficient specializes to one for a rank-one toric
point. The torsion slice may live on a base change of the original model. -/
theorem rankOne_special_coefficient_eq_one [IsIntegral (H ⊗ puncturedLine k).left] (n : ℕ)
    (hpm : (multiplyBy H n).left ≫ p = p ≫ (multiplyBy G n).left)
    (hc : Function.Surjective G.hom.appTop)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ puncturedLine k) (y : 𝟙_ (Over (Spec (.of k))) ⟶ H)
    (hx : x ^ n = 1) (hy : y ^ n = 1)
    {X : Scheme.{0}} (g : Spec (.of k) ⟶ X) (t m : X ⟶ X) (ht : t ≫ m = m)
    (c : X ⟶ G.left) (a : X ⟶ (G ⊗ G).left)
    (hm : m ≫ a = a ≫ (powerFirst G n).left)
    (hb : a ≫ (powerSecond G n).left = c ≫ (firstAxis G).left)
    (ha : a ≫ (fst G G).left = c)
    (hgc : g ≫ c = j ≫ η[G].left)
    (hgtc : (g ≫ t) ≫ c = x.left ≫ d.left ≫ p)
    (hgy : g ≫ a ≫ (snd G G).left = y.left ≫ p)
    (hgty : (g ≫ t) ≫ a ≫ (snd G G).left = y.left ≫ p)
    (M : (G ⊗ G).left.Modules)
    (J : (pullback (powerFirst G n).left).obj M ≅ (pullback (powerSecond G n).left).obj M)
    (e₁ : unit G.left ≅ (pullback (firstAxis G).left).obj M)
    (e₂ : unit G.left ≅ (pullback (secondAxis G).left).obj M)
    (hE : pullFramedAlong η[G].left (firstAxis G).left e₁ ≪≫
      (pullbackCongr (congrArg Over.Hom.left (axisOrigin_eq G))).app M =
        pullFramedAlong η[G].left (secondAxis G).left e₂)
    (α : unit (H ⊗ puncturedLine k).left ≅
      (pullback (toricProductMap G H (puncturedLine k) j p hp d)).obj M)
    (hα₁ : pullFramedAlong (torusAxis H (puncturedLine k)).left
        (toricProductMap G H (puncturedLine k) j p hp d) α ≪≫
      (pullbackCongr (torusAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη)).app M =
        pullFramedAlong (d.left ≫ p) (firstAxis G).left e₁)
    (hα₂ : pullFramedAlong (groupAxis H (puncturedLine k)).left
        (toricProductMap G H (puncturedLine k) j p hp d) α ≪≫
      (pullbackCongr (groupAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη)).app M =
        pullFramedAlong p (secondAxis G).left e₂) :
    g.appTop (wf t m ht ((pullback a).obj M)
      (sliceComparisonTriv m a (c ≫ (firstAxis G).left) (powerFirst G n).left (powerSecond G n).left
        hm hb M J (pullFramedAlong c (firstAxis G).left e₁))) = 1 := by
  let T := puncturedLine k
  let i := toricProductMap G H T j p hp d
  let v₀ := (lift y η[T] : 𝟙_ (Over (Spec (.of k))) ⟶ H ⊗ T).left
  let v₁ := (lift y x : 𝟙_ (Over (Spec (.of k))) ⟶ H ⊗ T).left
  have hηp : η[T].left ≫ d.left ≫ p = j ≫ η[G].left := by
    rw [← Category.assoc, ← Over.comp_left, IsMonHom.one_hom, hη]
  have hv₀ : v₀ ≫ i = g ≫ a :=
    point_comp_toricProductMap G H j p hp d η[T] y g a (by rw [ha, hgc, hηp]) hgy
  have hv₁ : v₁ ≫ i = (g ≫ t) ≫ a :=
    point_comp_toricProductMap G H j p hp d x y (g ≫ t) a (by rw [ha, hgtc]) hgty
  let hl := toricProductMap_powerFirst G H T j p hp d n hpm
  let hr := toricProductMap_powerSecond G H T j p hp d n hpm
  let b₀ := (firstAxis G).left
  let b := c ≫ b₀
  let e := pullFramedAlong c b₀ e₁
  let mr := (groupDilation H T n).left
  let r := (powerSecond G n).left
  have hframe (z : 𝟙_ (Over (Spec (.of k))) ⟶ T)
      (s : Spec (.of k) ⟶ X) (hz : z.left ≫ d.left ≫ p = s ≫ c)
      (w : Spec (.of k) ⟶ (H ⊗ T).left) (hw : w = (lift y z).left)
      (hwi : w ≫ i = s ≫ a) :
      pullFramedAlong s b e ≪≫
        (pullbackCongr (show s ≫ b = (w ≫ i) ≫ r by rw [hwi, Category.assoc, hb])).app M =
        evalFrameOnComposite w i mr r hr M α := by
    have he := pullFramedAlong_comp_of_agreement z.left (torusAxis H T).left (d.left ≫ p)
      i b₀ (torusAxis_comp_toricProductMap G H T j p hp d hη) α e₁ hα₁
    have hw' : w ≫ mr = z.left ≫ (torusAxis H T).left := by
      rw [hw]
      exact congrArg Over.Hom.left (point_comp_groupDilation H z y n hy)
    let target := (w ≫ i) ≫ r
    have htar : s ≫ b = target := by rw [show target = (w ≫ i) ≫ r from rfl, hwi, Category.assoc, hb]
    have htar' : (s ≫ c) ≫ b₀ = target := (Category.assoc s c b₀).trans htar
    have hz' : z.left ≫ (d.left ≫ p) = s ≫ c := hz
    have htarz : (z.left ≫ (d.left ≫ p)) ≫ b₀ = target :=
      (congrArg (· ≫ b₀) hz').trans htar'
    have htarr : (w ≫ mr) ≫ i = target :=
      (Category.assoc w mr i).trans ((congrArg (w ≫ ·) hr.symm).trans (Category.assoc w i r).symm)
    have htarz' : (z.left ≫ (torusAxis H T).left) ≫ i = target :=
      (congrArg (· ≫ i) hw'.symm).trans htarr
    have hL : pullFramedAlong s b e ≪≫ (pullbackCongr htar).app M =
        pullFramedAlong (s ≫ c) b₀ e₁ ≪≫ (pullbackCongr htar').app M := by
      change pullFramedAlong s (c ≫ b₀) (pullFramedAlong c b₀ e₁) ≪≫ _ = _
      rw [pullFramedAlong_comp s c b₀ e₁]
      apply Iso.ext
      simp [pullbackCongr_hom_app]
    have hR : evalFrameOnComposite w i mr r hr M α =
        pullFramedAlong (z.left ≫ (torusAxis H T).left) i α ≪≫ (pullbackCongr htarz').app M := by
      rw [evalFrameOnComposite_eq]
      exact framedAlong_move hw' i target α htarr htarz'
    have hM : pullFramedAlong (z.left ≫ (torusAxis H T).left) i α ≪≫ (pullbackCongr htarz').app M =
        pullFramedAlong (s ≫ c) b₀ e₁ ≪≫ (pullbackCongr htar').app M := by
      have he' := congrArg (fun e => e ≪≫ (pullbackCongr htarz).app M) he
      have hm' := framedAlong_move hz' b₀ target e₁ htarz htar'
      rw [← hm', ← he']
      apply Iso.ext
      simp [pullbackCongr_hom_app]
    exact hL.trans (hR.trans hM).symm
  have he₀ := hframe η[T] g (hηp.trans hgc.symm) v₀ rfl hv₀
  have he₁ := hframe x (g ≫ t) hgtc.symm v₁ rfl hv₁
  apply wf_eval_eq_one_of_framed_comparison g t m ht v₀ v₁ i a b _ r
    hm hb hv₀ hv₁ (torusDilation H T n).left mr hl hr M J α e he₀ he₁
  · exact congrArg Over.Hom.left (points_comp_torusDilation_eq H η[T] x y n
      (by rw [MonObj.one_eq_one, one_pow]) hx)
  · let u := pullUnitIso η[G].left (firstAxisDefect G n M J e₁)
    let q := (H ⊗ T).hom
    have hvq₁ : v₁ ≫ q = 𝟙 (Spec (.of k)) := Over.w (lift y x)
    have hvq₀ : v₀ ≫ q = 𝟙 (Spec (.of k)) := Over.w (lift y η[T])
    rw [toricComparison_scalar G H j p hp d hη n hpm hc M J e₁ e₂ hE α hα₁ hα₂]
    change pullUnitIso v₁ (pullUnitIso (q ≫ j) u) = pullUnitIso v₀ (pullUnitIso (q ≫ j) u)
    rw [pullUnitIso_comp v₁ (q ≫ j) u, pullUnitIso_comp v₀ (q ≫ j) u,
      ← Category.assoc v₁ q j, ← Category.assoc v₀ q j, hvq₁, hvq₀]

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.rankOne_special_coefficient_eq_one
