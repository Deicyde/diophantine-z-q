import ZInQKernel.Contrib.OneProof.RC.EvenJoin.CuspidalInventory
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.MovingCuspidal
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Joined
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

/-! The moving and unary weight-two products in the joined expansion are
cuspidal separately. Thus the actual blocks need no Eisenstein column. -/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion EvenMoving
open EvenUnary (evenUnaryStageLaw sievedCharacter weightedTheta unaryFun_eq_weightedTheta)
open CongruenceSubgroup Matrix.SpecialLinearGroup ModularForm UpperHalfPlane Filter
open ThetaCoeff Wiring AppE
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open scoped MatrixGroups Topology

/-- Multiplication by ordinary theta takes the half-integral cusp
vanishing to the weight-two cusp condition. -/
theorem theta_product_cuspidal {m : ℕ} {g : ℍ → ℂ} {f : WeightTwo m}
    (hf : (⇑f : ℍ → ℂ) = g * PrintsAnalytic.thetaFun) (hθ : OrdinaryThetaLaw)
    (hg : ∀ γ : SL(2, ℤ), IsZeroAtImInfty (cuspNorm (3 / 2) g γ)) :
    f.IsCuspForm := by
  apply (ModularForm.isCuspForm_iff f).mpr
  intro c hc
  have hSL : IsCusp c 𝒮ℒ := hc.mono (Subgroup.map_le_range (mapGL ℝ) (Gamma1 m))
  apply (OnePoint.isZeroAt_iff_forall_SL2Z hSL).mpr
  intro γ _
  have he (z : ℍ) : ‖(((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ) z)‖ =
      cuspNorm (3 / 2) g γ z * cuspNorm (1 / 2) PrintsAnalytic.thetaFun γ z := by
    rw [hf, SL_slash_apply, norm_mul, norm_zpow, Pi.mul_apply, norm_mul, cuspNorm, cuspNorm]
    have hr : ‖denom γ z‖ ^ (-(2 : ℤ)) =
        ‖denom γ z‖ ^ (-(3 / 2 : ℝ)) * ‖denom γ z‖ ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add (norm_pos_iff.mpr (denom_ne_zero _ _))]
      norm_num [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    rw [hr]
    ring
  obtain ⟨B, A, hB⟩ := isBoundedAtImInfty_iff.mp (hθ.cusps γ)
  have hbounded : IsBoundedUnder (· ≤ ·) atImInfty (norm ∘ cuspNorm (1 / 2) PrintsAnalytic.thetaFun γ) :=
    ⟨B, eventually_map.mpr (atImInfty_mem _ |>.mpr ⟨A, fun z hz => by
      change ‖cuspNorm (1 / 2) PrintsAnalytic.thetaFun γ z‖ ≤ B
      exact hB z hz⟩)⟩
  change Tendsto ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ) atImInfty (nhds 0)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := hg γ
  change Tendsto (cuspNorm (3 / 2) g γ) atImInfty (nhds 0) at ht
  simpa only [he] using ht.zero_mul_isBoundedUnder_le hbounded

private theorem weightTwoBlock_cuspidal {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ} {a : ℕ → ℂ}
    {f : WeightTwo m}
    (hfour : 4 ∣ m)
    (h : HasThreeHalvesExpansion (RingHom.id ℂ) m ξ a)
    (hzero : ∃ g, Series a g ∧ ∀ γ : SL(2, ℤ), IsZeroAtImInfty (cuspNorm (3 / 2) g γ))
    (hq : ∀ n, (qExpansion 1 f).coeff n = timesTheta a n) : f.IsCuspForm := by
  obtain ⟨g, hg, hs⟩ := h
  obtain ⟨g', hs', hz⟩ := hzero
  have he : g = g' := funext fun z => (hs' z).unique (by simpa only [RingHom.id_apply] using hs z) |>.symm
  obtain ⟨f', hf', _⟩ := theta_product_modular hfour ordinaryThetaLaw hg
  have hff : f = f' := ModularForm.qExpansion_injective one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map m) (PowerSeries.ext fun n => by
      rw [hq n]
      change _ = (qExpansion 1 (⇑f' : ℍ → ℂ)).coeff n
      rw [hf', qExpansion_theta_product (RingHom.id ℂ) hg.holo hs n, RingHom.id_apply])
  rw [hff]
  exact theta_product_cuspidal hf' ordinaryThetaLaw (he.symm ▸ hz)

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}

private theorem unaryFun_zeroAtCusps (hS : SupportSpec W) (i : Fin 2)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    {j : ℕ} (hj : 0 < j) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (cuspNorm (3 / 2)
      (unaryFun (evenTypes W.S hS.1).Good P.phaseData.η i j) γ) := by
  let B := P.phaseData.N * conductor W.S
  let hN : P.phaseData.N ∣ B := dvd_mul_right _ _
  let h4 : 4 ∣ B := P.phaseData.hN.trans hN
  let v := sievedCharacter P.phaseData.η hN h4 i
  let _ : NeZero B := ⟨mul_ne_zero (even_level_ne_zero P) (conductor_pos hS.1).ne'⟩
  have he : unaryFun (evenTypes W.S hS.1).Good P.phaseData.η i j =
      fun z : ℍ => (1 / 2 : ℂ) * weightedTheta v (2 * (j : ℂ) * (z : ℂ)) :=
    funext (unaryFun_eq_weightedTheta P hS i hodd hj)
  rw [he]
  change Tendsto _ atImInfty (nhds 0)
  have ht : Tendsto (cuspNorm (3 / 2)
      (fun z => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ) atImInfty (nhds 0) :=
    weightedTheta_zeroAtCusps v hj γ
  rw [show cuspNorm (3 / 2) (fun z => (1 / 2 : ℂ) * weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ =
      (fun z => ‖(1 / 2 : ℂ)‖ * cuspNorm (3 / 2)
        (fun w => weightedTheta v (2 * (j : ℂ) * (w : ℂ))) γ z) from by
    funext z
    simp only [cuspNorm, norm_mul, mul_assoc]]
  simpa only [mul_zero] using ht.const_mul ‖(1 / 2 : ℂ)‖

/-- Return the actual moving and unary blocks with their intrinsic
nebentypus, cusp vanishing and every Fourier coefficient. -/
theorem actual_cuspidal_blocks (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    ∃ (χB : DirichletCharacter ℂ (movingLevel P U))
      (χJ : ∀ j : ↥(subscripts U), DirichletCharacter ℂ (maskedLevel P * j.val))
      (fB : WeightTwo (movingLevel P U))
      (fJ : ∀ j : ↥(subscripts U), WeightTwo (maskedLevel P * j.val)),
      IsMovingCharacter P U χB ∧ (∀ j, IsUnaryCharacter P i j.val (χJ j)) ∧
      fB ∈ modFormCharSpace 2 χB.toUnitHom ∧
      (∀ j, fJ j ∈ modFormCharSpace 2 (χJ j).toUnitHom) ∧
      fB.IsCuspForm ∧ (∀ j, (fJ j).IsCuspForm) ∧
      (∀ n, (qExpansion 1 fB).coeff n =
        timesTheta (TL (fun p => P.phaseData.η p) U.toList P.sievedCoeff) n) ∧
      (∀ j n, (qExpansion 1 (fJ j)).coeff n =
        timesTheta (unaryCoeff (evenTypes W.S hS.1).Good (fun p => P.phaseData.η p) i j.val) n) ∧
      assembleForm P U fB fJ = joinedForm hS i U hU hodd := by
  have hmov := evenMovingSieve P hS U hU
  have hun (j : ℕ) (hj : j ∈ subscripts U) : EvenUnaryStageLaw P hS i j :=
    evenUnaryStageLaw P hS i (Nat.pos_of_ne_zero
      ((mem_subscripts (fun p hp => (hU p hp).1) j).mp hj).1.ne_zero)
  obtain ⟨χB, χJ, fB, fJ, f, hf, hχB, hχJ, hmB, hmJ, _, hqB, hqJ, hq⟩ :=
    evenWeightTwo hS i U hU hmov hodd hun
  refine ⟨χB, χJ, fB, fJ, hχB, hχJ, hmB, hmJ, ?_, ?_, hqB, hqJ, ?_⟩
  · obtain ⟨_, _, h⟩ := hmov
    exact weightTwoBlock_cuspidal ((evenMasked P hS).1.trans (dvd_mul_right _ _))
      h (exists_cuspidal_moving_series P hS U hU) hqB
  · intro j
    have hj : 0 < j.val := Nat.pos_of_ne_zero
      ((mem_subscripts (fun p hp => (hU p hp).1) j.val).mp j.property).1.ne_zero
    let _ : NeZero P.phaseData.N := ⟨even_level_ne_zero P⟩
    obtain ⟨ξ, _, hx⟩ := hun j.val j.property hodd
    have hs := unary_hasSum (evenTypes W.S hS.1).Good P.phaseData.η i hj
    exact weightTwoBlock_cuspidal
      (a := unaryCoeff (evenTypes W.S hS.1).Good (fun p => P.phaseData.η p) i j.val)
      ((evenMasked P hS).1.trans (dvd_mul_right _ _)) ⟨_, hx, hs⟩ ⟨_, fun z => by simpa only [RingHom.id_apply] using hs z,
        unaryFun_zeroAtCusps hS i hodd hj⟩ (hqJ j)
  · rw [← hf]
    exact ModularForm.qExpansion_injective one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _) (PowerSeries.ext fun n => by
        rw [hq n, joinedForm_coeff hS i U hU hodd n])

end ZInQ.Manuscript.RC.EvenJoin
