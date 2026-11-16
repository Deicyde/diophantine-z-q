import ZInQKernel.Contrib.OneProof.PicDictionary

noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PicDict
open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing
variable {K : Type} [Field K]

lemma famMap_eq (A : AbVar K) (f : A.X ⟶ A.X) : famMap f (ptK K) = (f ▷ ptK K).left := by
  apply Limits.pullback.hom_ext <;> simp

lemma transl_famMap (A : AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] (x : A.Pt (AlgebraicClosure K)) :
    transl x ≫ (f ▷ ptK K) = (f ▷ ptK K) ≫ transl (x ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transl, Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    rw [← Category.assoc, ← CategoryTheory.Hom.mul_def, MonObj.mul_comp, ← CategoryTheory.Hom.mul_def,
      MonObj.comp_mul]
    simp
  · simp [transl]

lemma famMap_mulN (A : AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] (n : ℕ) :
    (f ▷ ptK K) ≫ mulN A n = mulN A n ≫ (f ▷ ptK K) := by
  unfold mulN
  rw [← comp_whiskerRight, ← comp_whiskerRight]
  congr 1
  rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma famMap_constK (A : AbVar K) (f : A.X ⟶ A.X) (u : AlgebraicClosure K) :
    (famMap f (ptK K)).appTop (constK A u) = constK A u := by
  have hs : famMap f (ptK K) ≫ Limits.pullback.snd A.X.hom (ptK K).hom =
      Limits.pullback.snd A.X.hom (ptK K).hom := by simp
  simp only [constK, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]

lemma famMap_dualTors {A : AbVar K} (f : End A) {n : ℕ} {c : (AK A).Pic} (hc : IsDualTors n c) :
    IsDualTors n (Scheme.Pic.map (famMap f.hom (ptK K)) c) := by
  refine ⟨fun z => ?_, ?_⟩
  · have h1 : trl z ≫ famMap f.hom (ptK K) = famMap f.hom (ptK K) ≫ trl (z ≫ f.hom) := by
      rw [famMap_eq, ← Over.comp_left, ← Over.comp_left, transl_famMap]
    rw [← Scheme.Pic.map_comp, h1, Scheme.Pic.map_comp, hc.1]
  · rw [← Scheme.Pic.mapHom_apply, ← map_pow, hc.2, map_one]

/-- **`MumfordWeilDual` from `MumfordWeilPairing`** (transport along `f × 1`). -/
theorem mumfordWeilDual_of_pairing (h20a : MumfordWeilPairing) : MumfordWeilDual := by
  intro K _ A n hn hnK f x c hc ψ ψ'
  have hb : famMap f.hom (ptK K) ≫ mlN A n = mlN A n  ≫ famMap f.hom (ptK K) := by
    rw [famMap_eq, ← Over.comp_left, ← Over.comp_left, famMap_mulN]
  have ha : trl (Additive.toMul (x : P A))  ≫ famMap f.hom (ptK K) = famMap f.hom (ptK K) ≫ trl (Additive.toMul ((torsMap f n x : tors A n) : P A)) := by
    rw [famMap_eq, ← Over.comp_left, ← Over.comp_left, transl_famMap]
    rfl
  let e : (Scheme.Modules.pullback (famMap f.hom (ptK K))).obj (mod c) ≅ mod (Scheme.Pic.map (famMap f.hom (ptK K)) c) := (Scheme.Pic.mkIso _).symm
  let ψ'' : Triv A n (Scheme.Pic.map (famMap f.hom (ptK K)) c) :=
    Transport.transTriv (famMap f.hom (ptK K)) (mlN A n) hb (mod c) ψ' ≪≫ (Scheme.Modules.pullback (mlN A n)).mapIso e
  have hc' := famMap_dualTors f hc
  rw [(h20a K A n hn hnK x x _ _ hc' hc').1 ψ ψ'']
  obtain ⟨u, -, hu⟩ := (h20a K A n hn hnK (torsMap f n x) (torsMap f n x) c c hc hc).2.1 ψ'
  have h1 := Transport.wf_iso (trl (Additive.toMul (x : P A))) (mlN A n) (transl_left_comp_mulN_left x) e
    (Transport.transTriv (famMap f.hom (ptK K)) (mlN A n) hb (mod c) ψ')
  have h2 := Transport.wf_transport (trl (Additive.toMul (x : P A))) (famMap f.hom (ptK K)) (mlN A n)
    (trl (Additive.toMul ((torsMap f n x : tors A n) : P A))) ha hb
    (transl_left_comp_mulN_left (torsMap f n x)) (transl_left_comp_mulN_left x) (mod c) ψ'
  rw [weilFormula_eq_wf, h1, h2, ← weilFormula_eq_wf, ← hu]
  exact famMap_constK A f.hom u

end PicDict
