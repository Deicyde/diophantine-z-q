import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Forms

/-! The exact integral expansion comparisons at the chosen odd stage (tex 9486–9498,
9614–9636, 9647–9648, 9681–9693, 9913–9918). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open ZInQ.Manuscript.RC.Odd ThetaCoeff
open scoped Classical

variable {O K : Type} [CommRing O] [IsDomain O] [CharZero O] [Field K] [CharZero K]
  [Algebra O K]
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing O M)}
  {δ : ℤ} {adm : ℕ → Prop}
variable (E : Lift S) (D : Divisions E δ W R adm)

/-- Products of the distinct good-prime operators are independent of the enumeration. -/
theorem tl_eq_raw {U : Finset ℕ} (hU : ∀ p ∈ U, S.Good p) (J : List ℕ)
    (hJ : J.Nodup) (hJU : J.toFinset = U) : TL E.η J E.aθ = E.raw U := by
  unfold Lift.raw
  have perm := List.perm_of_nodup_nodup_toFinset_eq hJ (U.sort_nodup (· ≤ ·))
    (hJU.trans (U.sort_toFinset (· ≤ ·)).symm)
  have hprime : ∀ p ∈ J, Nat.Prime p := fun p hp =>
    S.good_prime p (hU p (hJU ▸ List.mem_toFinset.mpr hp))
  clear hJU hU
  generalize U.sort (· ≤ ·) = L at perm ⊢
  induction perm with
  | nil => rfl
  | cons p perm ih =>
    rw [TL_cons, TL_cons, ih (List.nodup_cons.mp hJ).2
      (fun p hp => hprime p (List.mem_cons_of_mem _ hp))]
  | swap p q L =>
    have hp := hprime p (by simp)
    have hq := hprime q (by simp)
    have hqp : q ≠ p := by
      intro e
      subst q
      exact (List.nodup_cons.mp hJ).1 (by simp)
    simp only [TL_cons]
    exact Top_comm _ hq.pos hp.pos ((hq.coprime_iff_not_dvd).mpr
      (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))) _ _
  | trans p₁ p₂ ihp ihq =>
    rw [ihp hJ hprime, ihq (p₁.nodup_iff.mp hJ) (fun p hp => hprime p (p₁.mem_iff.mpr hp))]

/-- Away from the unary support, the actual integral coefficient of `H_U`
is precisely the normalized lift of the undivided operator coefficient. -/
theorem hu_off_unary {U : Finset ℕ} (hu : Admissible S W U) (J : List ℕ)
    (hJ : J.Nodup) (hJU : J.toFinset = U) {n : ℕ} (hn : ¬ oddPart n ⊆ U) :
    algebraMap O K (E.HU D hu n) =
      (2 : K) ^ (-(δ + (U.card : ℤ) + 1)) * algebraMap O K (TL E.η J E.aθ n) := by
  have hz : ∑ j ∈ subscripts U, E.B D hu j * E.unary j n = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (mem_subscripts (fun p hp => S.good_prime p (hu.2 p hp)) j).mp hj
    rw [E.unary_off, mul_zero]
    intro k e
    by_cases hk : k = 0
    · subst k
      simp at e
      exact hn (e ▸ (by simp [oddPart] : oddPart 0 ⊆ U))
    · exact hn (by rw [e, oddPart_mul_sq hj'.1.ne_zero hk, oddPart_of_squarefree hj'.1]
                   exact hj'.2)
  have hH := congrArg (algebraMap O K) (HU_spec E D hu n)
  have hB := congrArg (algebraMap O K) (B_spec E D hu n)
  simp only [hz, sub_zero, map_mul, map_pow, map_ofNat] at hH hB
  rw [tl_eq_raw E hu.2 J hJ hJU]
  let k : ℤ := nU δ U
  change (2 : K) * algebraMap O K (E.HU D hu n) = _ at hH
  change (2 : K) ^ k.toNat * algebraMap O K (E.B D hu n) =
    (2 : K) ^ (-k).toNat * algebraMap O K (E.raw U n) at hB
  change _ = (2 : K) ^ (-(k + 1)) * _
  have htwo : (2 : K) ≠ 0 := by norm_num
  apply mul_left_cancel₀ (a := (2 : K) ^ (k.toNat + 1 : ℕ)) (pow_ne_zero _ htwo)
  calc
    _ = (2 : K) ^ k.toNat * ((2 : K) * algebraMap O K (E.HU D hu n)) := by
      rw [pow_succ, mul_assoc]
    _ = (2 : K) ^ (-k).toNat * algebraMap O K (E.raw U n) := hH ▸ hB
    _ = _ := by
      rw [← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ htwo]
      congr 2
      omega

/-- Multiplication by ordinary theta changes an integral coefficient by a multiple of two. -/
theorem fourierF_sub_hu {U : Finset ℕ} (hu : Admissible S W U) (n : ℕ) :
    (2 : O) ∣ E.FourierF D hu n - E.HU D hu n := by
  unfold Lift.FourierF timesTheta
  rw [add_sub_cancel_left]
  exact dvd_mul_right _ _

/-- A fresh coefficient of the actual divided form is the normalized
source at the squarefree product. This uses no recurrence on the lifts. -/
theorem hu_fresh {U : Finset ℕ} (hu : Admissible S W U) {q : ℕ}
    (hq : q.Prime) (hqU : q ∉ U) :
    algebraMap O K (E.HU D hu q) =
      (2 : K) ^ (-(δ + (U.card : ℤ) + 1)) * algebraMap O K (E.aθ ((∏ s ∈ U, s) * q)) := by
  have hn (p : ℕ) (hp : p ∈ U.toList) : ¬ p ∣ q := fun hd =>
    hqU ((Nat.prime_dvd_prime_iff_eq (S.good_prime p (hu.2 p (Finset.mem_toList.mp hp))) hq).mp
      hd ▸ Finset.mem_toList.mp hp)
  have hf := TL_fresh E.η E.aθ U.toList
    (fun p hp => S.good_prime p (hu.2 p (Finset.mem_toList.mp hp))) U.nodup_toList hn
  rw [Finset.prod_toList] at hf
  rw [hu_off_unary E D hu U.toList U.nodup_toList (Finset.toList_toFinset U)
    (theta_index_ne_fresh hq hqU), hf]

#print axioms tl_eq_raw
#print axioms hu_off_unary
#print axioms fourierF_sub_hu
#print axioms hu_fresh

end ZInQ.Manuscript.RC.O12Theta
