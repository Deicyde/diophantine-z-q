import ZInQKernel.Contrib.OneProof.PicDictionary

noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry Opposite

namespace PicDict.Transport
open Scheme.Modules

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v
variable {X : Scheme.{v}}

/-- **Coherence (III).** -/
lemma coherence_III (t g m t' : X ⟶ X) (ha : t ≫ g = g ≫ t') (h : t' ≫ m = m)
    (h₂ : t ≫ (g ≫ m) = g ≫ m) (M : X.Modules) :
    (Niso t g t' ha).inv.app ((Scheme.Modules.pullback m).obj M) ≫
        (Scheme.Modules.pullback t).map ((pullbackComp g m).hom.app M) ≫
          (pullbackComp t (g ≫ m)).hom.app M ≫ (pullbackCongr h₂).hom.app M ≫
            (pullbackComp g m).inv.app M =
      (Scheme.Modules.pullback g).map
        ((pullbackComp t' m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [Niso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, pullbackCongr_hom_app, pullbackCongr_inv_app]
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t' m M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₂ t g m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp ha.symm m M)]
  simp

/-- **Transport, second form**: pulling a trivialization back along `g` computes the formula for `g ≫ m`. -/
theorem wf_transport₂ (t g m t' : X ⟶ X) (ha : t ≫ g = g ≫ t') (h : t' ≫ m = m)
    (h₂ : t ≫ (g ≫ m) = g ≫ m) (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t (g ≫ m) h₂ M ((pOU g).symm ≪≫ (Scheme.Modules.pullback g).mapIso ψ ≪≫ (pullbackComp g m).app M) =
      g.appTop (wf t' m h M ψ) := by
  simp only [wf, unitHomAddEquiv_apply]
  rw [← pOU_conj g]
  congr 2
  have nat := (Niso t g t' ha).hom.naturality ψ.hom
  have e1 : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback g).map ψ.hom) =
      (Niso t g t' ha).hom.app _ ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback t').map ψ.hom) ≫
        (Niso t g t' ha).inv.app _ := by
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, ← nat]; simp
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [e1]
  simp only [Category.assoc]
  rw [reassoc_of% (coherence_I t g t' ha)]
  have h3 := coherence_III t g m t' ha h h₂ M
  simp only [Functor.map_comp] at h3
  rw [reassoc_of% h3]

lemma wf_congr_m (t : X ⟶ X) {m m' : X ⟶ X} (e : m = m') (h : t ≫ m = m) (h' : t ≫ m' = m')
    (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t m' h' M (ψ ≪≫ (pullbackCongr e).app M) = wf t m h M ψ := by
  subst e
  simp [wf, pullbackCongr]

end

end PicDict.Transport

namespace PicDict
open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing MonoidalCategory
open scoped CategoryTheory.MonObj
variable {K : Type} [Field K]

lemma mulN_mul (A : AbVar K) (m n : ℕ) : mlN A (m * n) = mlN A m ≫ mlN A n := by
  show (mulN A (m * n)).left = (mulN A m ≫ mulN A n).left
  congr 1
  unfold mulN
  rw [← comp_whiskerRight, MonObj.comp_pow, Category.comp_id, ← pow_mul]

lemma transl_mulN (A : AbVar K) (m : ℕ) (x : A.Pt (AlgebraicClosure K)) :
    transl x ≫ mulN A m = mulN A m ≫ transl (x ^ m) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transl, mulN, Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    rw [← Category.assoc, ← CategoryTheory.Hom.mul_def, MonObj.comp_pow, Category.comp_id, mul_pow,
      ← CategoryTheory.Hom.mul_def, MonObj.comp_mul]
    simp [MonObj.comp_pow]
  · simp [transl, mulN]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma mulN_constK (A : AbVar K) (m : ℕ) (u : AlgebraicClosure K) :
    (mlN A m).appTop (constK A u) = constK A u := by
  have hs : mlN A m ≫ Limits.pullback.snd A.X.hom (ptK K).hom = Limits.pullback.snd A.X.hom (ptK K).hom := by
    show (mulN A m).left ≫ (CartesianMonoidalCategory.snd A.X (ptK K)).left =
      (CartesianMonoidalCategory.snd A.X (ptK K)).left
    rw [← Over.comp_left]
    unfold mulN
    rw [CartesianMonoidalCategory.whiskerRight_snd]
  simp only [constK, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]

/-- **`MumfordWeilCompat` from `MumfordWeilPairing`** (transport along `m_A`). -/
theorem mumfordWeilCompat_of_pairing (h20a : MumfordWeilPairing) : MumfordWeilCompat := by
  intro K _ A m n hm hn hmnK x c hc ψ ψ'
  have hnK : (n : K) ≠ 0 := by intro h; apply hmnK; rw [Nat.cast_mul, h, mul_zero]
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hc' : IsDualTors (m * n) c := ⟨hc.1, by rw [mul_comm, pow_mul, hc.2, one_pow]⟩
  have ha : trl (Additive.toMul (x : P A)) ≫ mlN A m =
      mlN A m ≫ trl (Additive.toMul ((torsSmul A m n x : tors A n) : P A)) := by
    rw [← Over.comp_left, ← Over.comp_left, transl_mulN]
    rfl
  have h₂ : trl (Additive.toMul (x : P A)) ≫ (mlN A m ≫ mlN A n) = mlN A m ≫ mlN A n := by
    rw [← mulN_mul]; exact transl_left_comp_mulN_left x
  let ψ₂ := (Transport.pOU (mlN A m)).symm ≪≫ (Scheme.Modules.pullback (mlN A m)).mapIso ψ' ≪≫
    (Scheme.Modules.pullbackComp (mlN A m) (mlN A n)).app (mod c)
  let ψ₃ : Triv A (m * n) c := ψ₂ ≪≫ (Scheme.Modules.pullbackCongr (mulN_mul A m n).symm).app (mod c)
  rw [(h20a K A (m * n) hmn hmnK x x c c hc' hc').1 ψ ψ₃]
  obtain ⟨u, -, hu⟩ := (h20a K A n hn hnK (torsSmul A m n x) (torsSmul A m n x) c c hc hc).2.1 ψ'
  have h1 := Transport.wf_congr_m (trl (Additive.toMul (x : P A))) (mulN_mul A m n).symm h₂
    (transl_left_comp_mulN_left x) (mod c) ψ₂
  have h2 := Transport.wf_transport₂ (trl (Additive.toMul (x : P A))) (mlN A m) (mlN A n)
    (trl (Additive.toMul ((torsSmul A m n x : tors A n) : P A))) ha
    (transl_left_comp_mulN_left (torsSmul A m n x)) h₂ (mod c) ψ'
  rw [weilFormula_eq_wf, h1, h2, ← weilFormula_eq_wf, ← hu]
  exact mulN_constK A m u

end PicDict
