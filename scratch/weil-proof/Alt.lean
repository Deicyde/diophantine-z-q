import ZInQKernel.Contrib.OneProof.WeilFormulaTheta

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace WeilProof.Theta

open PicDict PkgI3 PkgI3.AbVar MonoidalCategory Scheme.Modules PicDict.Transport
open scoped CategoryTheory.MonObj

local notation "PB" => Scheme.Modules.pullback

lemma isIso_pw {X : Scheme.{0}} {N : X.Modules} {s : X ⟶ X} (b : (PB s).obj N ⟶ N) [IsIso b] :
    ∀ j, IsIso (pw N b j)
  | 0 => by change IsIso b; infer_instance
  | j + 1 => by
    have := isIso_pw b j
    change IsIso (prod N (pw N b j) b)
    simp only [prod]
    infer_instance

/-- **The core of Mumford §23** on a scheme `X`: `t = s^n` (as lifts' base), `t ≫ m = m`,
`m ≫ t = s ≫ m`, translations fixing `Γ(X, 𝒪)`, `L` with `m^*L` invertible, `Φ ⊗ L ≅ t^*L`. -/
theorem alt_core {X : Scheme.{0}} {m t s : X ⟶ X} (h : t ≫ m = m) (hb : m ≫ t = s ≫ m)
    (hab : t ≫ s = s ≫ t) (hs : ∀ r : Γ(X, ⊤), s.appTop r = r)
    (hr : (pOU t).inv = Functor.LaxMonoidal.ε (PB t)) (j₀ : ℕ) (hpow : powM s j₀ = t)
    (L Φ : X.Modules) [((PB m).obj L).IsInvertible] {N' : X.Modules}
    (jN : (PB m).obj L ⊗ N' ≅ 𝟙_ X.Modules)
    (ψ : unit X ≅ (PB m).obj Φ) (w : Φ ⊗ L ≅ (PB t).obj L) :
    val (alpha t m h Φ ψ) = 1 := by
  let u : (PB m).obj L ⟶ (PB m).obj (Φ ⊗ L) :=
    (λ_ ((PB m).obj L)).inv ≫ (ψ.hom ▷ (PB m).obj L) ≫ Functor.LaxMonoidal.μ (PB m) Φ L
  let β : (PB m).obj L ⟶ (PB s).obj ((PB m).obj L) := u ≫ (PB m).map w.hom ≫ rhoAB hb L
  let EA : (PB m).obj L ⟶ (PB m).obj L :=
    (λ_ ((PB m).obj L)).inv ≫ (alpha t m h Φ ψ ▷ (PB m).obj L) ≫ (λ_ ((PB m).obj L)).hom
  have R : (PB t).map β ≫ swapAB hab ((PB m).obj L) ≫ (PB s).map (thetaT h L) =
      thetaT h L ≫ EA ≫ β := by
    have trel := tensor_relation pullbackCompMonoidal_proof h hr Φ L ψ
    have nat : (PB t).map ((PB m).map w.hom) ≫ thetaT h ((PB t).obj L) =
        thetaT h (Φ ⊗ L) ≫ (PB m).map w.hom := by
      have n1 := (pullbackComp t m).hom.naturality w.hom
      have n2 := (pullbackCongr h).hom.naturality w.hom
      simp only [Functor.comp_map] at n1 n2
      simp only [thetaT, ← Category.assoc, n1]
      simp only [Category.assoc, n2]
    have tro := theta_rho h hb hab L
    simp only [β, u, EA, Functor.map_comp, Category.assoc]
    rw [← tro, reassoc_of% nat]
    simp only [Functor.map_comp, Category.assoc] at trel
    rw [reassoc_of% trel]
    simp [MonoidalCategory.comp_whiskerRight]
  -- β is an isomorphism
  have : IsIso β := by
    simp only [β, u, rhoAB]
    infer_instance
  have hθ : IsIso (thetaT h L) := by
    simp only [thetaT]
    infer_instance
  set b := inv β with hbdef
  -- (C1): the commutator of `θ` and `b` is `EA⁻¹`
  have C1 : prod ((PB m).obj L) (thetaT h L) b ≫ EA =
      mv ((PB m).obj L) hab.symm (prod ((PB m).obj L) b (thetaT h L)) := by
    have R' : swapAB hab ((PB m).obj L) ≫ (PB s).map (thetaT h L) ≫ b =
        (PB t).map b ≫ thetaT h L ≫ EA := by
      rw [← cancel_epi ((PB t).map β), reassoc_of% R, hbdef, IsIso.hom_inv_id, Category.comp_id,
        ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [prod, mv, Category.assoc]
    rw [← R']
    simp only [swapAB, pullbackCongr_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  -- (C2): the theta argument
  have cp := comm_pw hs b j₀
  have cm := comm_mv_left hpow hab.symm cp
  have hpwi : IsIso (pw ((PB m).obj L) b j₀) := isIso_pw b j₀
  have hmvi : IsIso (mv ((PB m).obj L) hpow (pw ((PB m).obj L) b j₀)) := by
    simp only [mv]; infer_instance
  obtain ⟨lam, hlam⟩ := exists_eq_smulHom ((PB m).obj L)
    (inv (thetaT h L) ≫ mv ((PB m).obj L) hpow (pw ((PB m).obj L) b j₀))
  have hmv : mv ((PB m).obj L) hpow (pw ((PB m).obj L) b j₀) =
      thetaT h L ≫ ((PB m).obj L).smulHom lam := by
    rw [← hlam, IsIso.hom_inv_id_assoc]
  obtain ⟨mu, hmu⟩ := exists_eq_smulHom ((PB m).obj L)
    (inv (inv (thetaT h L) ≫ mv ((PB m).obj L) hpow (pw ((PB m).obj L) b j₀)))
  have hunit : mu * lam = 1 := by
    apply eq_of_smulHom_eq ((PB m).obj L)
    rw [smulHom_mul, ← hlam, ← hmu, IsIso.hom_inv_id, smulHom_one]
  rw [hmv] at cm
  have C2 := comm_smul_left hs ⟨lam, mu, by rw [mul_comm, hunit], hunit⟩ cm
  -- combine
  have hEA : EA = 𝟙 _ := by
    unfold Comm at C2
    rw [smulHom_one, Category.comp_id] at C2
    have hpi : IsIso (prod ((PB m).obj L) (thetaT h L) b) := by simp only [prod]; infer_instance
    rw [← cancel_epi (prod ((PB m).obj L) (thetaT h L) b), C1, ← C2, Category.comp_id]
  have hAN : alpha t m h Φ ψ ▷ (PB m).obj L = 𝟙 _ := by
    have := congrArg (fun φ => (λ_ ((PB m).obj L)).hom ≫ φ ≫ (λ_ ((PB m).obj L)).inv) hEA
    simp only [EA, Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.id_comp] at this
    exact (Category.comp_id _).symm.trans this
  have hA : alpha t m h Φ ψ = 𝟙 _ := unit_endo_eq_id_of_whisker (C := X.Modules) _ jN hAN
  rw [hA]
  rfl

variable {k : Type} [Field k]

/-- **Mumford §23 (`e_n(x, φ_L(x)) = 1`) from divisibility.** -/
theorem mumfordWeilAltAC_of_div (hdiv : DivisibleAC) : MumfordWeilAltAC := by
  intro k _ _ X n hn hnk c₀ x hx ψ
  obtain ⟨y, rfl⟩ := hdiv k X n hn hnk x
  have h : (AC.tr (y ^ n)).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
    rw [← Over.comp_left, AC.tr_comp_mul _ hx]
  have hb : (AC.mul X n).left ≫ (AC.tr (y ^ n)).left = (AC.tr y).left ≫ (AC.mul X n).left := by
    rw [← Over.comp_left, ← Over.comp_left, tr_mul_comm]
  have hab : (AC.tr (y ^ n)).left ≫ (AC.tr y).left = (AC.tr y).left ≫ (AC.tr (y ^ n)).left := by
    rw [← Over.comp_left, ← Over.comp_left, AC.tr_comp_tr, AC.tr_comp_tr, mul_comm]
  have hr : (pOU (AC.tr (y ^ n)).left).inv = Functor.LaxMonoidal.ε (PB (AC.tr (y ^ n)).left) := by
    have h1 := unitRatio_tr pullbackCompMonoidal_proof X (y ^ n) hx
    have h2 : unitRatio (AC.tr (y ^ n)).left = 𝟙 _ :=
      (unitHomAddEquiv (unit X.X.left)).injective (h1.trans id_val.symm)
    have h3 := congrArg (· ≫ Functor.LaxMonoidal.ε (PB (AC.tr (y ^ n)).left)) h2
    simp only [unitRatio, Category.assoc, Category.id_comp] at h3
    rw [← Functor.Monoidal.εIso_hom, Iso.inv_hom_id] at h3
    exact (Category.comp_id _).symm.trans h3
  have hpow : powM (AC.tr y).left (n - 1) = (AC.tr (y ^ n)).left := by
    rw [powM_tr, Nat.sub_add_cancel hn]
  have hcl : AC.phi c₀ (y ^ n) * c₀ = Scheme.Pic.map (AC.tr (y ^ n)).left c₀ := by
    simp only [AC.phi, inv_mul_cancel_right]
  let w : AC.modX (AC.phi c₀ (y ^ n)) ⊗ AC.modX c₀ ≅ (PB (AC.tr (y ^ n)).left).obj (AC.modX c₀) :=
    (Scheme.Pic.mulIso _ _).symm ≪≫ eqToIso (congrArg (fun c : X.X.left.Pic => (fromSkeleton X.X.left.Modules).obj c.val) hcl) ≪≫
      Scheme.Pic.mkIso _
  let jN : (PB (AC.mul X n).left).obj (AC.modX c₀) ⊗
      (fromSkeleton X.X.left.Modules).obj ((Scheme.Pic.map (AC.mul X n).left c₀)⁻¹).val ≅ 𝟙_ X.X.left.Modules :=
    ((Scheme.Pic.mkIso _).symm ⊗ᵢ Iso.refl _) ≪≫ (Scheme.Pic.mulIso _ _).symm ≪≫
      eqToIso (congrArg (fun c : X.X.left.Pic => (fromSkeleton X.X.left.Modules).obj c.val) (mul_inv_cancel _)) ≪≫ Scheme.Pic.oneIso
  unfold AC.formula
  rw [wf_eq_alpha]
  exact alt_core h hb hab (tr_appTop X y) hr (n - 1) hpow (AC.modX c₀) (AC.modX (AC.phi c₀ (y ^ n))) jN ψ w

end WeilProof.Theta
