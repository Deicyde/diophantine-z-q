import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationSigned
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassForms
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Basic

/-!
# Genuine lower-level signed torsion correlations

All-label raw torsion forms have the actual row covariance. The embedded
lower-level points are fixed under their principal group, and the full
n-torsion kernel is permuted. This proves lower-level modularity, with
holomorphy and all cusp bounds inherited from actual upper-level forms.
-/

noncomputable section

set_option maxHeartbeats 1200000

open Complex Function Set Finset
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm Manifold

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationLower

open TorsionCorrelation TorsionCorrelationEnlarge TorsionCorrelationRows
open TorsionCorrelationModular TorsionCorrelationSigned DivisionSeriesMembership
open ThetaFiveTorsion (act act_mul act_one)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The actual right row action on ambient torsion classes. -/
def pointAction (M : ℕ) (γ : SL(2, ℤ)) (P : Point M) : Point M :=
  (P.1 * (γ 0 0 : ZMod M) + P.2 * (γ 1 0 : ZMod M),
    P.1 * (γ 0 1 : ZMod M) + P.2 * (γ 1 1 : ZMod M))

lemma pointAction_label (M : ℕ) (γ : SL(2, ℤ)) (a b : ℤ) :
    pointAction M γ (label M a b) = label M (act (a,b) γ).1 (act (a,b) γ).2 := by
  apply Prod.ext <;> simp [pointAction, label, act]

/-- The row action is additive, with no covariance premise. -/
def pointActionHom (M : ℕ) (γ : SL(2, ℤ)) : Point M →+ Point M where
  toFun := pointAction M γ
  map_zero' := by apply Prod.ext <;> simp [pointAction]
  map_add' P Q := by apply Prod.ext <;> simp [pointAction, add_mul] <;> ring

lemma pointAction_mul {M : ℕ} (hM : 0 < M) (γ δ : SL(2, ℤ)) (P : Point M) :
    pointAction M δ (pointAction M γ P) = pointAction M (γ * δ) P := by
  obtain ⟨a, b, rfl⟩ := label_surjective hM P
  rw [pointAction_label, pointAction_label, pointAction_label]
  rw [← act_mul]

lemma pointAction_one {M : ℕ} (hM : 0 < M) (P : Point M) : pointAction M 1 P = P := by
  obtain ⟨a, b, rfl⟩ := label_surjective hM P
  rw [pointAction_label, act_one]

/-- Inverse matrices give an actual equivalence of residue points. -/
def pointActionEquiv {M : ℕ} (hM : 0 < M) (γ : SL(2, ℤ)) : Point M ≃ Point M where
  toFun := pointAction M γ
  invFun := pointAction M γ⁻¹
  left_inv P := by rw [pointAction_mul hM, mul_inv_cancel, pointAction_one hM]
  right_inv P := by rw [pointAction_mul hM, inv_mul_cancel, pointAction_one hM]

lemma pointAction_add (M : ℕ) (γ : SL(2, ℤ)) (P Q : Point M) :
    pointAction M γ (P + Q) = pointAction M γ P + pointAction M γ Q :=
  (pointActionHom M γ).map_add P Q

lemma pointAction_sub (M : ℕ) (γ : SL(2, ℤ)) (P Q : Point M) :
    pointAction M γ (P - Q) = pointAction M γ P - pointAction M γ Q :=
  map_sub (pointActionHom M γ) P Q

lemma pointAction_nsmul (M : ℕ) (γ : SL(2, ℤ)) (n : ℕ) (P : Point M) :
    pointAction M γ (n • P) = n • pointAction M γ P := map_nsmul (pointActionHom M γ) n P

lemma pointAction_zsmul (M : ℕ) (γ : SL(2, ℤ)) (s : ℤ) (P : Point M) :
    pointAction M γ (s • P) = s • pointAction M γ P := map_zsmul (pointActionHom M γ) s P

/-- The positive level embedding commutes with the actual right row action. -/
theorem pointAction_levelMap {M : ℕ} (hM : 0 < M) (k : ℕ) (γ : SL(2, ℤ)) (P : Point M) :
    pointAction (k * M) γ (levelMap k M hM P) = levelMap k M hM (pointAction M γ P) := by
  obtain ⟨a, b, rfl⟩ := label_surjective hM P
  rw [levelMap_label hM, pointAction_label, pointAction_label, levelMap_label hM]
  congr 1 <;> dsimp [act] <;> ring

/-- A principal matrix fixes every class at its principal level. -/
theorem pointAction_Gamma (M : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M)
    (P : Point M) : pointAction M γ P = P := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  apply Prod.ext <;> simp [pointAction, h00, h01, h10, h11]

/-- Embedded lower-level classes are fixed at the upper level by the lower principal group. -/
theorem embedded_fixed {ℓ : ℕ} (hℓ : 0 < ℓ) (n : ℕ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma ℓ) (A : Point ℓ) :
    pointAction (n * ℓ) γ (levelMap n ℓ hℓ A) = levelMap n ℓ hℓ A := by
  rw [pointAction_levelMap hℓ, pointAction_Gamma ℓ γ hγ]

/-- Divisible labels stay divisible under the actual integral row action. -/
lemma bad_act {M : ℕ} {a b : ℤ} (hbad : (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) (γ : SL(2, ℤ)) :
    (M : ℤ) ∣ (act (a,b) γ).1 ∧ (M : ℤ) ∣ (act (a,b) γ).2 := by
  exact ⟨dvd_add (dvd_mul_of_dvd_left hbad.1 _) (dvd_mul_of_dvd_left hbad.2 _),
    dvd_add (dvd_mul_of_dvd_left hbad.1 _) (dvd_mul_of_dvd_left hbad.2 _)⟩

/-- The actual all-label raw function, including the zero extension. -/
def regFun (M : ℕ) (v : ℤ × ℤ) : ℍ → ℂ :=
  fun τ => TorsionDistributionTwo.reg M v.1 v.2 τ

/-- Full integral special-linear covariance from the proved Good F law and the bad-label cases. -/
theorem regFun_slash {M : ℕ} (hM : 0 < M) (γ : SL(2, ℤ)) (v : ℤ × ℤ) :
    regFun M v ∣[(1 : ℤ)] γ = regFun M (act v γ) := by
  obtain ⟨a,b⟩ := v
  by_cases hbad : (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b
  · have hbad' := bad_act hbad γ
    funext τ
    rw [ModularForm.SL_slash_apply]
    simp only [regFun, TorsionDistributionTwo.reg_of_bad hbad,
      TorsionDistributionTwo.reg_of_bad hbad', zero_mul]
  · have hgood : AllLevelForms.Good M (a,b) := hbad
    have hgood' := AllLevelForms.good_act hgood γ
    have hleft : regFun M (a,b) = AllLevelForms.F M (a,b) := by
      funext τ
      exact TorsionDistributionTwo.reg_of_good hbad τ
    have hright : regFun M (act (a,b) γ) = AllLevelForms.F M (act (a,b) γ) := by
      funext τ
      exact TorsionDistributionTwo.reg_of_good hgood' τ
    rw [hleft, hright]
    exact AllLevelForms.F_slash hM γ (a,b) hgood

/-- All-label class covariance in the actual raw normalization. -/
theorem h_slash {M : ℕ} (hM : 0 < M) (γ : SL(2, ℤ)) (P : Point M) :
    (fun τ => h M τ P) ∣[(1 : ℤ)] γ = fun τ => h M τ (pointAction M γ P) := by
  obtain ⟨a,b,rfl⟩ := label_surjective hM P
  have hl : (fun τ => h M τ (label M a b)) = regFun M (a,b) :=
    funext fun τ => h_label hM τ a b
  have hr : (fun τ => h M τ (pointAction M γ (label M a b))) = regFun M (act (a,b) γ) := by
    rw [pointAction_label]
    exact funext fun τ => h_label hM τ _ _
  rw [hl, hr]
  exact regFun_slash hM γ (a,b)

/-- The actual raw h-form is the known all-label λ-form divided by its nonzero common scale. -/
def rawForm (M : ℕ) (hM : 0 < M) (P : Point M) : _root_.ModularForm (ΓP M) 1 :=
  TorsionWeierstrassData.scale⁻¹ • WeierstrassForms.lambdaForm M hM (P.1.val : ℤ) (P.2.val : ℤ)

lemma rawForm_apply (M : ℕ) (hM : 0 < M) (P : Point M) (τ : ℍ) : rawForm M hM P τ = h M τ P := by
  change TorsionWeierstrassData.scale⁻¹ *
    WeierstrassForms.lambdaForm M hM (P.1.val : ℤ) (P.2.val : ℤ) τ = _
  rw [WeierstrassForms.lambdaForm_apply, TorsionWeierstrassData.lambdaValue]
  exact inv_mul_cancel_left₀ TorsionWeierstrassData.scale_ne_zero _

/-- The actual raw h-form has full all-label special-linear covariance. -/
theorem rawForm_slash (M : ℕ) (hM : 0 < M) (γ : SL(2, ℤ)) (P : Point M) :
    (⇑(rawForm M hM P)) ∣[(1 : ℤ)] γ = ⇑(rawForm M hM (pointAction M γ P)) := by
  have hleft : ⇑(rawForm M hM P) = fun τ => h M τ P :=
    funext fun τ => rawForm_apply M hM P τ
  have hright : ⇑(rawForm M hM (pointAction M γ P)) = fun τ => h M τ (pointAction M γ P) :=
    funext fun τ => rawForm_apply M hM (pointAction M γ P) τ
  rw [hleft, hright]
  exact h_slash hM γ P

/-- Actual product of two raw forms as a weight-two form, including bad classes. -/
def rawProductForm (M : ℕ) (hM : 0 < M) (P Q : Point M) : WeightTwo M :=
  _root_.ModularForm.mcast (by norm_num) ((rawForm M hM P).mul (rawForm M hM Q))

lemma rawProductForm_apply (M : ℕ) (hM : 0 < M) (P Q : Point M) (τ : ℍ) :
    rawProductForm M hM P Q τ = h M τ P * h M τ Q := by
  change rawForm M hM P τ * rawForm M hM Q τ = _
  rw [rawForm_apply, rawForm_apply]

/-- The actual signed correlation is already a genuine upper-level modular form. -/
def upperCorrelationForm (M : ℕ) (hM : 0 < M) (n : ℕ) (s : ℤ) (A B : Point M) : WeightTwo M :=
  ∑ T : DivisionIndex n,
    rawProductForm M hM (A + divisionPoint M n T) (B - s • divisionPoint M n T)

lemma upperCorrelationForm_apply (M : ℕ) (hM : 0 < M) (n : ℕ) (s : ℤ)
    (A B : Point M) (τ : ℍ) : upperCorrelationForm M hM n s A B τ = CInt M τ n s A B := by
  simp only [upperCorrelationForm, _root_.sum_apply, rawProductForm_apply, CInt]

/-- The full actual torsion kernel is preserved and permuted by each special-linear matrix. -/
def kernelPerm {M : ℕ} (hM : 0 < M) (n : ℕ) (γ : SL(2, ℤ)) :
    torsionKernel M n ≃ torsionKernel M n where
  toFun P := ⟨pointAction M γ P.1, by
    have hp : n • P.1 = 0 := P.2
    change n • pointAction M γ P.1 = 0
    rw [← pointAction_nsmul, hp]
    exact (pointActionHom M γ).map_zero⟩
  invFun P := ⟨pointAction M γ⁻¹ P.1, by
    have hp : n • P.1 = 0 := P.2
    change n • pointAction M γ⁻¹ P.1 = 0
    rw [← pointAction_nsmul, hp]
    exact (pointActionHom M γ⁻¹).map_zero⟩
  left_inv P := by
    apply Subtype.ext
    change pointAction M γ⁻¹ (pointAction M γ P.1) = P.1
    rw [pointAction_mul hM, mul_inv_cancel, pointAction_one hM]
  right_inv P := by
    apply Subtype.ext
    change pointAction M γ (pointAction M γ⁻¹ P.1) = P.1
    rw [pointAction_mul hM, inv_mul_cancel, pointAction_one hM]

/-- Reindexing permutation of the exact n² finite indices via the genuine torsion kernel. -/
def divisionPerm {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (hnM : n ∣ M) (γ : SL(2, ℤ)) :
    DivisionIndex n ≃ DivisionIndex n :=
  (divisionEquiv hM hn hnM).trans ((kernelPerm hM n γ).trans (divisionEquiv hM hn hnM).symm)

lemma divisionPerm_spec {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (hnM : n ∣ M)
    (γ : SL(2, ℤ)) (T : DivisionIndex n) :
    divisionPoint M n (divisionPerm hM hn hnM γ T) = pointAction M γ (divisionPoint M n T) := by
  exact congrArg Subtype.val
    ((divisionEquiv hM hn hnM).apply_symm_apply (kernelPerm hM n γ (divisionEquiv hM hn hnM T)))

/-- Full covariance of the actual signed correlation, including its genuine torsion reindexing. -/
theorem CInt_slash {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (hnM : n ∣ M)
    (γ : SL(2, ℤ)) (s : ℤ) (A B : Point M) :
    (fun τ => CInt M τ n s A B) ∣[(2 : ℤ)] γ =
      fun τ => CInt M τ n s (pointAction M γ A) (pointAction M γ B) := by
  let e : DivisionIndex n ≃ DivisionIndex n := divisionPerm hM hn hnM γ
  have ht (T : DivisionIndex n) :
      (fun τ => h M τ (A + divisionPoint M n T) * h M τ (B - s • divisionPoint M n T))
        ∣[(2 : ℤ)] γ =
      (fun τ => h M τ (pointAction M γ A + divisionPoint M n (e T)) *
        h M τ (pointAction M γ B - s • divisionPoint M n (e T))) := by
    change (((fun τ => h M τ (A + divisionPoint M n T)) *
      (fun τ => h M τ (B - s • divisionPoint M n T))) ∣[(1 + 1 : ℤ)] γ) = _
    rw [ModularForm.mul_slash_SL2, h_slash hM, h_slash hM]
    have ha : pointAction M γ (A + divisionPoint M n T) =
        pointAction M γ A + divisionPoint M n (e T) := by
      rw [pointAction_add, divisionPerm_spec hM hn hnM γ]
    have hb : pointAction M γ (B - s • divisionPoint M n T) =
        pointAction M γ B - s • divisionPoint M n (e T) := by
      rw [pointAction_sub, pointAction_zsmul, divisionPerm_spec hM hn hnM γ]
    rw [ha, hb]
    rfl
  funext τ
  rw [ModularForm.SL_slash_apply]
  unfold CInt
  rw [Finset.sum_mul]
  have heq (T : DivisionIndex n) :
      (h M (γ • τ) (A + divisionPoint M n T) * h M (γ • τ) (B - s • divisionPoint M n T)) *
        UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) (τ : ℂ) ^ (-(2 : ℤ)) =
      h M τ (pointAction M γ A + divisionPoint M n (e T)) *
        h M τ (pointAction M γ B - s • divisionPoint M n (e T)) := by
    have hh := congrFun (ht T) τ
    rw [ModularForm.SL_slash_apply] at hh
    exact hh
  calc
    _ = ∑ T : DivisionIndex n, h M τ (pointAction M γ A + divisionPoint M n (e T)) *
        h M τ (pointAction M γ B - s • divisionPoint M n (e T)) :=
      Finset.sum_congr rfl (fun T _ => heq T)
    _ = _ := e.sum_comp (fun T => h M τ (pointAction M γ A + divisionPoint M n T) *
      h M τ (pointAction M γ B - s • divisionPoint M n T))

/-- Lower principal invariance of the actual upper signed-correlation function. -/
theorem embedded_CInt_invariant {ℓ n : ℕ} (hℓ : 0 < ℓ) (hn : 0 < n)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma ℓ) (s : ℤ) (A B : Point ℓ) :
    (fun τ => CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)) ∣[(2 : ℤ)] γ =
      (fun τ => CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)) := by
  rw [CInt_slash (Nat.mul_pos hn hℓ) hn (dvd_mul_right n ℓ),
    embedded_fixed hℓ n γ hγ A, embedded_fixed hℓ n γ hγ B]

/-- The upper correlation form is proved invariant under the lower mapped principal group. -/
theorem upper_embedded_invariant {ℓ n : ℕ} (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) :
    ∀ γ ∈ (ΓP ℓ),
      (⇑(upperCorrelationForm (n * ℓ) (Nat.mul_pos hn hℓ) n s
        (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B))) ∣[(2 : ℤ)] γ =
        ⇑(upperCorrelationForm (n * ℓ) (Nat.mul_pos hn hℓ) n s
          (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)) := by
  intro γ hγ
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  have heq : ⇑(upperCorrelationForm (n * ℓ) (Nat.mul_pos hn hℓ) n s
      (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)) =
      fun τ => CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B) :=
    funext fun τ => upperCorrelationForm_apply _ _ _ _ _ _ τ
  rw [heq]
  have hh := embedded_CInt_invariant hℓ hn g hg s A B
  rw [ModularForm.SL_slash] at hh
  exact hh

/-- All cusps of the lower positive principal level are actual cusps of the upper level. -/
theorem common_cusps {ℓ n : ℕ} (hℓ : 0 < ℓ) (hn : 0 < n) :
    ∀ c, IsCusp c (ΓP ℓ) → IsCusp c (ΓP (n * ℓ)) := by
  have : NeZero ℓ := ⟨hℓ.ne'⟩
  have : NeZero (n * ℓ) := ⟨(Nat.mul_pos hn hℓ).ne'⟩
  exact Subgroup.IsArithmetic.isCusp_of_isCusp

/-- Genuine weight-two correlation on the lower principal level, with every
field supplied from proved invariance and actual upper holomorphy/cusp bounds. -/
def lowerCorrelationForm (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) : WeightTwo ℓ where
  toFun := fun τ => CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    have hh := embedded_CInt_invariant hℓ hn g hg s A B
    rw [ModularForm.SL_slash] at hh
    exact hh
  holo' := by
    change MDiff (fun τ => CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B))
    let f := upperCorrelationForm (n * ℓ) (Nat.mul_pos hn hℓ) n s
      (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)
    have heq : ⇑f = fun τ => CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B) :=
      funext fun τ => upperCorrelationForm_apply _ _ _ _ _ _ τ
    rw [← heq]
    exact f.holo'
  bdd_at_cusps' {c} hc := by
    let f := upperCorrelationForm (n * ℓ) (Nat.mul_pos hn hℓ) n s
      (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)
    have heq : ⇑f = fun τ => CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B) :=
      funext fun τ => upperCorrelationForm_apply _ _ _ _ _ _ τ
    rw [← heq]
    exact f.bdd_at_cusps' (common_cusps hℓ hn _ hc)

/-- The lower form's literal actual correlation value, for every signed slope and all classes. -/
theorem lowerCorrelationForm_apply (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) (τ : ℍ) :
    lowerCorrelationForm ℓ n hℓ hn s A B τ =
      CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B) := rfl

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationLower
