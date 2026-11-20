import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Shell

/-! Use the weighted comparison on the actual sieved unary series. Only
the scalar comparison of ordinary theta at two dilations is isolated. -/

noncomputable section
set_option maxHeartbeats 1200000

namespace ZInQ.Manuscript.RC.EvenUnary

open AddressGenuine AuxInputs BlocksPerU CongruenceSubgroup EvenBudget EvenExpansion
open ModularForm O12 PrintsAnalytic ThetaCoeff UpperHalfPlane Wiring
open Matrix.SpecialLinearGroup
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53
open scoped MatrixGroups Manifold ModularForm

/-- The scalar contributed by the dilation and the conversion to the
cube of the theta multiplier. -/
def shellScalar (m j : ℕ) [NeZero m] (h : 4 * j ∣ m) : DirichletCharacter ℂ m :=
  jacobiCharacter ((dvd_mul_right 4 j).trans h) (-(j : ℤ)) (by simpa using h)

/-- A comparison solely of the two ordinary unweighted theta ratios.
It has no weighted series, sieve, holomorphy or cusp hypothesis. -/
def OrdinaryDilationComparison (m j : ℕ) : Prop :=
  ∀ (hm : m ≠ 0) (h : 4 * j ∣ m),
    let _ : NeZero m := ⟨hm⟩
    ∀ (γ : ↥(Gamma0 m)) (z : ℍ),
      denom (γ : SL(2, ℤ)) z * dilatedThetaRatio j γ z =
        shellScalar m j h ((γ.val 1 1 : ℤ) : ZMod m) * thetaMultiplier γ z ^ 3

private theorem changeLevel_unit {B m : ℕ} (v : DirichletCharacter ℂ B)
    (hBM : B ∣ m) (d : ℤ) (hu : IsUnit (d : ZMod m)) :
    (v.changeLevel hBM) (d : ZMod m) = v (d : ZMod B) := by
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu.unit_spec,
    ZMod.cast_intCast hBM]

private theorem cusp_mul_half {f : ℍ → ℂ} {γ : SL(2, ℤ)}
    (h : IsBoundedAtImInfty (cuspNorm (3 / 2) f γ)) :
    IsBoundedAtImInfty (cuspNorm (3 / 2) (fun z => (1 / 2 : ℂ) * f z) γ) := by
  obtain ⟨K, t, hK⟩ := isBoundedAtImInfty_iff.mp h
  apply isBoundedAtImInfty_iff.mpr
  refine ⟨‖(1 / 2 : ℂ)‖ * K, t, fun z hz => ?_⟩
  have he : cuspNorm (3 / 2) (fun z => (1 / 2 : ℂ) * f z) γ z =
      ‖(1 / 2 : ℂ)‖ * cuspNorm (3 / 2) f γ z := by
    simp only [cuspNorm, norm_mul, mul_assoc]
  rw [he, norm_mul, Real.norm_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hK z hz) (norm_nonneg _)

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}

theorem evenUnaryStageLaw_of_ordinaryDilation (P : EvenSource W L τ) (hS : SupportSpec W)
    (i : Fin 2) {j : ℕ} (hj : 0 < j)
    (hθ : OrdinaryDilationComparison (maskedLevel P * j) j) :
    EvenUnaryStageLaw P hS i j := by
  intro hodd
  let B := P.phaseData.N * conductor W.S
  let m := maskedLevel P * j
  let hN : P.phaseData.N ∣ B := dvd_mul_right _ _
  let h4 : 4 ∣ B := P.phaseData.hN.trans hN
  have hB : B ≠ 0 := mul_ne_zero (even_level_ne_zero P) (conductor_pos hS.1).ne'
  let _ : NeZero B := ⟨hB⟩
  have hm : m ≠ 0 := mul_ne_zero (pow_ne_zero _ hB) hj.ne'
  let _ : NeZero m := ⟨hm⟩
  have hlev : 4 * B^2 * j ∣ m := Nat.mul_dvd_mul_right (four_mul_sq_dvd_cube h4) j
  have h4j : 4 * j ∣ m := (Nat.mul_dvd_mul_right (dvd_mul_right 4 (B^2)) j).trans hlev
  have hBM : B ∣ m := (dvd_pow_self _ (by decide : 3 ≠ 0)).trans (dvd_mul_right _ _)
  let v := sievedCharacter P.phaseData.η hN h4 i
  let q := shellScalar m j h4j
  let χ : DirichletCharacter ℂ m := v.changeLevel hBM * q
  have hv : v.Odd := sievedCharacter_odd _ _ _ _ hodd
  have heq : unaryFun (evenTypes W.S hS.1).Good P.phaseData.η i j =
      fun z : ℍ => (1 / 2 : ℂ) * weightedTheta v (2 * (j : ℂ) * (z : ℂ)) :=
    funext (unaryFun_eq_weightedTheta P hS i hodd hj)
  refine ⟨χ, ?_, ?_⟩
  · intro n hn
    have hnB : n.Coprime B := hn.coprime_dvd_right hBM
    have hunit : IsUnit ((n : ℤ) : ZMod m) := by
      rw [Int.cast_natCast, ZMod.isUnit_iff_coprime]
      exact hn
    change v.changeLevel hBM (n : ZMod m) * q n = _
    have hval := changeLevel_unit v hBM (n : ℤ) hunit
    simp only [Int.cast_natCast] at hval
    rw [hval, sievedCharacter_at_unit _ _ _ _ hnB]
    dsimp only [q, shellScalar]
    rw [jacobiCharacter_at_unit _ _ _ hn]
  rw [heq]
  refine ⟨mdifferentiable_const.mul (weightedTheta_holo v hj), ?_,
    fun γ => cusp_mul_half (weightedTheta_cusps v hj γ)⟩
  intro γ z
  let d := γ.val 1 1
  have hc : (m : ℤ) ∣ γ.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.property)
  have hc' : ((4 * B^2 * j : ℕ) : ℤ) ∣ γ.val 1 0 :=
    (show ((4 * B^2 * j : ℕ) : ℤ) ∣ (m : ℤ) by exact_mod_cast hlev).trans hc
  have hunit : IsUnit (d : ZMod m) := by
    rw [← Gamma0Map_apply γ, ← MonoidHom.coe_toHomUnits]
    exact ((Gamma0Map m).toHomUnits γ).isUnit
  rw [weightedTheta_relative v hv hj γ.val hc' z]
  have hval : (χ.toUnitHom ((Gamma0Map m).toHomUnits γ) : ℂ) = v d * q d := by
    rw [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    exact (MulChar.mul_apply ..).trans
      (congrArg (· * q d) (changeLevel_unit _ _ d hunit))
  rw [hval, mul_assoc (v _) (denom _ _) (dilatedThetaRatio _ _ _), hθ hm h4j γ z]
  ring

variable (hS : SupportSpec W) {B : ℕ} [NeZero (conductor W.S)]
variable {X : Model P hS B} [CharZero X.K] (A : FourierData X) (C : SourceAtPlace P X.O X.K)

/-- The fixed even expansion with the weighted unary comparison reduced
to the ordinary theta scalar. The constituent comparison refers to the
actual assembled weight-two form. -/
theorem evenExpansion_of_ordinaryDilation (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hB : EvenMovingSieveLaw P U)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (hθ : ∀ j ∈ subscripts U, OrdinaryDilationComparison (maskedLevel P * j) j) :
    ∃ f : WeightTwo (movingLevel P U),
      (∀ n, (qExpansion 1 f).coeff n =
        timesTheta (halfDivided (evenTypes W.S hS.1).Good (fun p => P.phaseData.η p)
          P.sievedCoeff P.δ i U.toList) n) ∧
      (∀ (κ : X.K →+* ℂ), κ.comp C.eK = C.eC →
        (∀ n, n ≠ 0 →
          κ (algebraMap X.O X.K (A.coeff n (X.F U))) = (qExpansion 1 f).coeff n) →
        ∀ n, n ≠ 0 → A.coeff n (X.F U) = timesTheta (evenH hS A C i U) n) := by
  have hU' (p : ℕ) (hp : p ∈ U) : p.Prime := (hU p hp).1
  have hJ (j : ℕ) (hj : j ∈ subscripts U) : EvenUnaryStageLaw P hS i j :=
    evenUnaryStageLaw_of_ordinaryDilation P hS i
      (Nat.pos_of_ne_zero ((mem_subscripts hU' j).mp hj).1.ne_zero) (hθ j hj)
  obtain ⟨_, _, _, _, f, _, _, _, _, _, _, _, _, hf⟩ := evenWeightTwo hS i U hU hB hodd hJ
  exact ⟨f, hf, fun κ hκ hcoord => evenExpansion hS A C i U hU f hf κ hκ hcoord⟩

end ZInQ.Manuscript.RC.EvenUnary
