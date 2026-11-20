import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.OrdinaryPhase

/-! Discharge the ordinary theta phase and hence the intrinsic-level
weighted unary input, keeping the moving and coordinate inputs separate. -/

noncomputable section
set_option maxHeartbeats 1200000

namespace ZInQ.Manuscript.RC.EvenUnary

open AddressGenuine AuxInputs BlocksPerU Complex CongruenceSubgroup EvenBudget EvenExpansion
open Matrix Matrix.SpecialLinearGroup ModularForm O12 PrintsAnalytic ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53
open scoped MatrixGroups ModularForm

private theorem theta_dilation_period (j : ℕ) (z : ℂ) (l : ℤ) :
    jacobiTheta (2 * (j : ℂ) * (z + (l : ℂ))) = jacobiTheta (2 * (j : ℂ) * z) := by
  have hθ : Function.Periodic jacobiTheta 2 := fun u => by rw [add_comm, jacobiTheta_two_add]
  have h := (hθ.int_mul ((j : ℤ) * l)) (2 * (j : ℂ) * z)
  convert h using 2
  push_cast
  ring

private theorem theta_dilation_ne (j : ℕ) (hj : 0 < j) (z : ℍ) :
    jacobiTheta (2 * (j : ℂ) * (z : ℂ)) ≠ 0 := by
  apply HalfIntegral.jacobiTheta_ne_zero_of_im_pos
  rw [show (2 * (j : ℂ)) = (((2 * (j : ℝ) : ℝ)) : ℂ) by simp, im_ofReal_mul]
  exact mul_pos (by positivity) z.im_pos

private theorem right_T_entries (γ : SL(2, ℤ)) (l : ℤ) :
    (γ * ModularGroup.T ^ l) 1 0 = γ 1 0 ∧
    (γ * ModularGroup.T ^ l) 1 1 = γ 1 1 + γ 1 0 * l := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem ordinaryDilation_nontriangular {m j : ℕ} [NeZero m]
    (hj : 0 < j) (h4j : 4*j ∣ m) (γ : ↥(Gamma0 m))
    (hc : γ.val 1 0 ≠ 0) (z : ℍ) :
    denom (γ : SL(2, ℤ)) z * dilatedThetaRatio j γ z =
      shellScalar m j h4j ((γ.val 1 1 : ℤ) : ZMod m) * thetaMultiplier γ z ^ 3 := by
  let c := γ.val 1 0
  let d := γ.val 1 1
  have hcM : (m : ℤ) ∣ c :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.property)
  have hdet : γ.val 0 0 * d - γ.val 0 1 * c = 1 := by
    have h := γ.val.det_coe
    rwa [det_fin_two] at h
  have hcd : IsCoprime d c := ⟨γ.val 0 0, -γ.val 0 1, by linear_combination hdet⟩
  have hcd' : IsCoprime d (c.natAbs : ℤ) := by
    rcases Int.natAbs_eq c with he | he
    · exact he ▸ hcd
    · have e : (c.natAbs : ℤ) = -c := by omega
      rw [e]
      exact (IsCoprime.neg_right_iff _ _).2 hcd
  obtain ⟨p, hp2, hp, hdp⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq 2 (Int.natAbs_ne_zero.mpr hc) hcd'
  have hdp' : c ∣ (p : ℤ) - d := Int.natAbs_dvd.mp hdp.symm.dvd
  obtain ⟨l, he⟩ := hdp'
  have heq : (p : ℤ) = d + c*l := by omega
  let δ : SL(2, ℤ) := γ.val * ModularGroup.T ^ l
  have hh := right_T_entries γ.val l
  have hδd : δ 1 1 = (p : ℤ) := by
    change (γ.val * ModularGroup.T ^ l) 1 1 = _
    exact hh.2.trans heq.symm
  have hδc : δ 1 0 = c := hh.1
  have hδm : δ ∈ Gamma0 m := by rw [Gamma0_mem, hδc]; exact Gamma0_mem.mp γ.property
  let δ₀ : ↥(Gamma0 m) := ⟨δ, hδm⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have h4δ : ((4*j : ℕ) : ℤ) ∣ δ 1 0 := by
    rw [hδc]
    exact (show ((4*j : ℕ) : ℤ) ∣ (m : ℤ) by exact_mod_cast h4j).trans hcM
  let w := ModularGroup.T ^ (-l) • z
  have hw : ModularGroup.T ^ l • w = z := by
    dsimp only [w]
    rw [← mul_smul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, one_smul]
  have hδz : δ • w = γ.val • z := by
    change (γ.val * ModularGroup.T ^ l) • w = _
    rw [mul_smul, hw]
  have hwz : (z : ℂ) = (w : ℂ) + (l : ℂ) := by
    rw [← hw, ModularGroup.coe_T_zpow_smul_eq]
  have hden : denom δ w = denom (γ : SL(2, ℤ)) z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, hδc, hδd, Int.cast_natCast, hwz]
    have hp' : (p : ℂ) = (d : ℂ) + (c : ℂ) * (l : ℂ) := by
      exact_mod_cast heq
    rw [hp']
    dsimp [d, c]
    ring
  have htd (r : ℕ) : dilatedThetaRatio r δ w = dilatedThetaRatio r γ z := by
    rw [dilatedThetaRatio, dilatedThetaRatio, hδz]
    congr 1
    rw [hwz, theta_dilation_period]
  have hJ : thetaMultiplier δ w = thetaMultiplier γ z := by
    simpa [dilatedThetaRatio, thetaMultiplier, thetaFun] using htd 1
  have hu : IsUnit (p : ZMod m) := by
    have hv := ((Gamma0Map m).toHomUnits δ₀).isUnit
    simpa only [MonoidHom.coe_toHomUnits, Gamma0Map_apply, hδd, Int.cast_natCast, δ₀] using hv
  have hpc := (ZMod.isUnit_iff_coprime p m).mp hu
  have hpodd := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hfac : p.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hpodd ∘ even_iff_two_dvd.mpr)
  have hq : shellScalar m j h4j (p : ZMod m) = (jacobiSym (-(j : ℤ)) p : ℂ) := by
    rw [shellScalar, jacobiCharacter_at_unit _ _ _ hpc, PrintsAnalytic.kronecker, hfac, pow_zero,
      pow_zero, Nat.div_one, one_mul]
  have hpd : (p : ZMod m) = (d : ZMod m) := by
    rw [← Int.cast_natCast, heq, Int.cast_add, Int.cast_mul, Gamma0_mem.mp γ.property,
      zero_mul, add_zero]
  have h := ordinaryPhase_prime (by omega : p ≠ 2) hj δ hδd h4δ w
  rw [hden, htd, hJ, ← hq, hpd] at h
  exact h

/-- The ordinary phase comparison at every matrix in the required level.
A right translation makes the lower-right entry an odd prime when the
lower-left entry is nonzero. -/
theorem ordinaryDilationComparison_proved (m : ℕ) {j : ℕ} (hj : 0 < j) :
    OrdinaryDilationComparison m j := by
  intro hm h4j inst γ z
  by_cases hc : γ.val 1 0 = 0
  · have hdet := γ.val.det_coe
    rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
    let d := γ.val 1 1
    let b := γ.val 0 1
    have hd : d = 1 ∨ d = -1 :=
      Int.isUnit_iff.mp ((Units.mkOfMulEqOne _ _ (mul_comm _ _ |>.trans hdet)).isUnit)
    have ha : (↑(γ.val • z) : ℂ) = (z : ℂ) + ((b*d : ℤ) : ℂ) := by
      rw [coe_specialLinearGroup_apply]
      rcases hd with hd | hd
      · have h := hd
        change γ.val 1 1 = 1 at h
        have ha : γ.val 0 0 = 1 := by simpa [h] using hdet
        simp [hc, h, ha, b, hd]
      · have h := hd
        change γ.val 1 1 = -1 at h
        have ha : γ.val 0 0 = -1 := by rw [h] at hdet; omega
        simp [hc, h, ha, b, hd]
        ring
    have hratio (r : ℕ) (hr : 0 < r) : dilatedThetaRatio r γ z = 1 := by
      rw [dilatedThetaRatio, ha, theta_dilation_period, div_self (theta_dilation_ne r hr z)]
    have hJ : thetaMultiplier γ z = 1 := by
      simpa [dilatedThetaRatio, thetaMultiplier, thetaFun] using hratio 1 (by decide)
    rw [hratio j hj, hJ, one_pow, mul_one, mul_one, ModularGroup.denom_apply, hc]
    simp only [Int.cast_zero, zero_mul, zero_add]
    change (d : ℂ) = shellScalar m j h4j (d : ZMod m)
    -- Compare a lower unipotent and its negative to read the sign at -1.
    let g : SL(2, ℤ) := ⟨!![(1 : ℤ), 0; (m : ℤ), 1], by simp [det_fin_two]⟩
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
    have hg : g ∈ Gamma0 m := by
      apply Gamma0_mem.mpr
      change ((m : ℤ) : ZMod m) = 0
      simp
    have hg' : -g ∈ Gamma0 m := by
      apply Gamma0_mem.mpr
      change ((-(m : ℤ) : ℤ) : ZMod m) = 0
      simp
    have he₁ := ordinaryDilation_nontriangular hj h4j ⟨g, hg⟩ (by exact hm') z
    have he₂ := ordinaryDilation_nontriangular hj h4j ⟨-g, hg'⟩ (by exact neg_ne_zero.mpr hm') z
    have hδ : denom ((-g : SL(2, ℤ)) : GL (Fin 2) ℝ) z = -denom g z := by
      rw [ModularGroup.denom_apply (-g) z, ModularGroup.denom_apply g z]
      change (↑(-(g 1 0)) : ℂ) * z + ↑(-(g 1 1)) = _
      push_cast; ring
    have hD : dilatedThetaRatio j (-g) z = dilatedThetaRatio j g z := by
      simp only [dilatedThetaRatio, ModularGroup.SL_neg_smul]
    have hT : thetaMultiplier (-g) z = thetaMultiplier g z := by
      simp only [thetaMultiplier, ModularGroup.SL_neg_smul]
    have hnonzero : thetaMultiplier g z ≠ 0 := by
      have h (u : ℍ) : thetaFun u ≠ 0 := by
        simpa [thetaFun] using theta_dilation_ne 1 (by decide) u
      exact div_ne_zero (h _) (h _)
    change denom g z * dilatedThetaRatio j g z =
      shellScalar m j h4j ((1 : ℤ) : ZMod m) * thetaMultiplier g z ^ 3 at he₁
    change denom ((-g : SL(2, ℤ)) : GL (Fin 2) ℝ) z * dilatedThetaRatio j (-g) z =
      shellScalar m j h4j ((-1 : ℤ) : ZMod m) * thetaMultiplier (-g) z ^ 3 at he₂
    rw [Int.cast_one, map_one, one_mul] at he₁
    simp only [Int.cast_neg, Int.cast_one] at he₂
    rw [hδ, hD, hT, neg_mul, he₁] at he₂
    have hsign : shellScalar m j h4j (-1 : ZMod m) = -1 := by
      apply mul_right_cancel₀ (pow_ne_zero 3 hnonzero)
      simpa only [neg_one_mul] using he₂.symm
    rcases hd with hd | hd <;> simp [hd, hsign]
  · exact ordinaryDilation_nontriangular hj h4j γ hc z


variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}

/-- The weighted Poisson law of the actual positive sieved unary shell,
at the intrinsic level and with the prescribed scalar on every unit. -/
theorem evenUnaryStageLaw (P : EvenSource W L τ) (hS : SupportSpec W)
    (i : Fin 2) {j : ℕ} (hj : 0 < j) :
    EvenUnaryStageLaw P hS i j :=
  evenUnaryStageLaw_of_ordinaryDilation P hS i hj (ordinaryDilationComparison_proved _ hj)

variable (hS : SupportSpec W) {B : ℕ} [NeZero (conductor W.S)]
variable {X : Model P hS B} [CharZero X.K] (A : FourierData X) (C : SourceAtPlace P X.O X.K)

/-- The fixed even expansion with the unary input discharged. The weight
two form is supplied, and the lattice identity uses its coordinates under
the chosen compatible complex embedding. -/
theorem evenExpansion_of_unary (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hB : EvenMovingSieveLaw P U)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    ∃ f : WeightTwo (movingLevel P U),
      (∀ n, (qExpansion 1 f).coeff n =
        timesTheta (halfDivided (evenTypes W.S hS.1).Good (fun p => P.phaseData.η p)
          P.sievedCoeff P.δ i U.toList) n) ∧
      (∀ (κ : X.K →+* ℂ), κ.comp C.eK = C.eC →
        (∀ n, n ≠ 0 →
          κ (algebraMap X.O X.K (A.coeff n (X.F U))) = (qExpansion 1 f).coeff n) →
        ∀ n, n ≠ 0 → A.coeff n (X.F U) = timesTheta (evenH hS A C i U) n) := by
  apply evenExpansion_of_ordinaryDilation hS A C i U hU hB hodd
  intro j hj
  exact ordinaryDilationComparison_proved _ (Nat.pos_of_ne_zero
    ((mem_subscripts (fun p hp => (hU p hp).1) j).mp hj).1.ne_zero)

end ZInQ.Manuscript.RC.EvenUnary
