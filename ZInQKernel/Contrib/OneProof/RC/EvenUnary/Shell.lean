import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Characters
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Resum

/-! Identifying the actual positive square-shell expansion with the
two-sided unary theta series (tex 9618–9622). -/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.EvenUnary

open AddressGenuine AuxInputs Complex EvenBudget EvenExpansion Function ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53
open scoped Real

private theorem shell_term {N : ℕ} (good : ℕ → Prop) (η : DirichletCharacter ℂ N) (i : Fin 2)
    {j k : ℕ} (hj : 0 < j) (hk : k ≠ 0) :
    unaryCoeff good (fun n => η n) i j (j * k ^ 2) =
      (by classical
          exact if ∀ p ∈ k.primeFactors, good p then η k * (unaryWeight i k : ℂ) else 0) := by
  classical
  by_cases hgood : ∀ p ∈ k.primeFactors, good p
  · let h : ∃ t : ℕ, t ≠ 0 ∧ (∀ p ∈ t.primeFactors, good p) ∧ j * k ^ 2 = j * t ^ 2 :=
      ⟨k, hk, hgood, rfl⟩
    rw [unaryCoeff, dite_eq_left h, ite_eq_left hgood]
    have he : k = h.choose :=
      Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
        (Nat.eq_of_mul_eq_mul_left hj h.choose_spec.2.2)
    rw [← he]
  · rw [unaryCoeff, ite_eq_right hgood, dite_eq_right]
    rintro ⟨t, _, ht, he⟩
    exact hgood ((Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
      (Nat.eq_of_mul_eq_mul_left hj he) : k = t).symm ▸ ht)

private theorem shell_reindex {N : ℕ} (good : ℕ → Prop) (η : DirichletCharacter ℂ N)
    (i : Fin 2) {j : ℕ} (hj : 0 < j) (z : ℍ) :
    unaryFun good η i j z =
      ∑' k : ℕ+, unaryCoeff good (fun n => η n) i j (j * (k : ℕ) ^ 2) *
        Periodic.qParam 1 (z : ℂ) ^ (j * (k : ℕ) ^ 2) := by
  have hinj : Function.Injective (fun k : ℕ+ => j * (k : ℕ) ^ 2) := by
    intro k l h
    apply Subtype.ext
    exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
      (Nat.eq_of_mul_eq_mul_left hj h)
  unfold unaryFun
  symm
  refine hinj.tsum_eq (f := fun n => unaryCoeff good (fun a => η a) i j n *
    Periodic.qParam 1 (z : ℂ) ^ n) ?_
  intro n hmem
  by_contra hn
  have hzero : unaryCoeff good (fun n => η n) i j n = 0 := by
    rw [unaryCoeff, dite_eq_right]
    rintro ⟨k, hk, _, rfl⟩
    exact hn ⟨⟨k, Nat.pos_of_ne_zero hk⟩, rfl⟩
  exact hmem (by simp [hzero])

private theorem jacobiTerm_shell (j k : ℕ) (z : ℍ) :
    jacobiTheta₂_term (k : ℤ) 0 (2 * (j : ℂ) * (z : ℂ)) =
      Periodic.qParam 1 (z : ℂ) ^ (j * k ^ 2) := by
  simp only [jacobiTheta₂_term, mul_zero, zero_add, Periodic.qParam, ofReal_one, div_one,
    ← exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The manuscript's sieved positive-frequency correction is half of the
two-sided theta with its odd coefficient character. This equality concerns
the actual convergent function consumed by the expansion. -/
theorem unaryFun_eq_weightedTheta {ℓ : ℕ} {W : WData ℓ}
    {L : CentralNormalization (Ecurve ℓ)} {τ : SqClass (conductor W.S)}
    (P : EvenSource W L τ) (hS : SupportSpec W) (i : Fin 2)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    {j : ℕ} (hj : 0 < j) (z : ℍ) :
    let B := P.phaseData.N * conductor W.S
    let h4 : 4 ∣ B := P.phaseData.hN.trans (dvd_mul_right _ _)
    let v := sievedCharacter P.phaseData.η (dvd_mul_right _ _) h4 i
    unaryFun (evenTypes W.S hS.1).Good P.phaseData.η i j z =
      (1 / 2 : ℂ) * weightedTheta v (2 * (j : ℂ) * (z : ℂ)) := by
  classical
  let B := P.phaseData.N * conductor W.S
  let hN : P.phaseData.N ∣ B := dvd_mul_right _ _
  let h4 : 4 ∣ B := P.phaseData.hN.trans hN
  let v := sievedCharacter P.phaseData.η hN h4 i
  let w := 2 * (j : ℂ) * (z : ℂ)
  let _ : NeZero B := ⟨mul_ne_zero (even_level_ne_zero P) (conductor_pos hS.1).ne'⟩
  change unaryFun _ _ _ _ _ = (1 / 2 : ℂ) * weightedTheta v w
  have hw : 0 < w.im := by
    rw [show w = (((2 * (j : ℝ) : ℝ)) : ℂ) * (z : ℂ) by simp [w]]
    exact (im_ofReal_mul _ _).symm ▸ mul_pos (by positivity) z.im_pos
  have hv : v (-1) = -1 := sievedCharacter_odd _ _ _ _ hodd
  let f (n : ℤ) := v (n : ZMod B) * ((n : ℂ) * jacobiTheta₂_term n 0 w)
  have hf : Summable f := (weightedTheta_hasSum v hw).summable
  have heven : f.Even := by
    intro n
    dsimp [f]
    rw [Int.cast_neg, Int.cast_neg, show (-(n : ZMod B)) = (-1) * n by ring, map_mul, hv]
    simp [jacobiTheta₂_term]
  have hzero : f 0 = 0 := by simp [f]
  have hsum : weightedTheta v w = 2 * ∑' k : ℕ+, f k := by
    change (∑' n : ℤ, f n) = _
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hf, hzero, zero_add]
    simp [two_mul]
  rw [hsum, shell_reindex _ _ _ hj]
  rw [← mul_assoc, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_mul]
  refine tsum_congr fun k => ?_
  let n : ℕ := k
  dsimp only [f]
  simp only [Int.cast_natCast]
  have hk : n ≠ 0 := k.pos.ne'
  have hgood := (good_factors_iff_coprime hS hk).trans (coprime_supportModulus P hS n).symm
  change unaryCoeff _ _ _ _ (j * n ^ 2) * Periodic.qParam 1 (z : ℂ) ^ (j * n ^ 2) =
    v n * ((n : ℂ) * jacobiTheta₂_term (n : ℤ) 0 w)
  rw [shell_term _ _ _ hj hk, if_congr hgood rfl rfl, show w = _ from rfl, jacobiTerm_shell]
  by_cases hn : n.Coprime B
  · rw [ite_eq_left hn, sievedCharacter_at_unit _ _ _ _ hn, unaryWeight]
    push_cast
    ring
  · have hu : ¬IsUnit (n : ZMod B) := fun h => hn ((ZMod.isUnit_iff_coprime n B).mp h)
    rw [ite_eq_right hn, MulChar.map_nonunit v hu, zero_mul, zero_mul]

end ZInQ.Manuscript.RC.EvenUnary
