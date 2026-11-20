import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Translate
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Assembly

/-! The fresh-prime comparison and its use in the fixed even expansion.
The unary transformation and the comparison of constituent coordinates
with the assembled form remain separate inputs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open AddressGenuine AuxInputs BlocksPerU CongruenceSubgroup EvenBudget EvenExpansion
open Matrix.SpecialLinearGroup ModularForm O12 PrintsAnalytic ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53
open Filter Asymptotics
open scoped MatrixGroups Manifold BigOperators ModularForm Topology

private theorem sub_smul_threeHalves {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ} {f g : ℍ → ℂ}
    (hf : HalfIntegralThreeHalves m ξ f) (hg : HalfIntegralThreeHalves m ξ g) (s : ℂ) :
    HalfIntegralThreeHalves m ξ (f - s • g) := by
  refine ⟨hf.holo.sub (mdifferentiable_const.mul hg.holo), ?_, ?_⟩
  · intro γ z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hf.law, hg.law]
    ring
  · intro γ
    have h₁ : BoundedAtFilter atImInfty (cuspNorm (3 / 2) f γ) := hf.cusps γ
    have h₂ : BoundedAtFilter atImInfty (cuspNorm (3 / 2) g γ) := hg.cusps γ
    have hb := h₁.add (BoundedAtFilter.smul ‖s‖ h₂)
    refine (isBigO_of_le atImInfty ?_).trans hb
    intro z
    have he : 0 ≤ cuspNorm (3/2) f γ z + ‖s‖ * cuspNorm (3/2) g γ z := by
      unfold cuspNorm
      positivity
    show ‖cuspNorm (3/2) (f - s • g) γ z‖ ≤
      ‖cuspNorm (3/2) f γ z + ‖s‖ * cuspNorm (3/2) g γ z‖
    rw [Real.norm_of_nonneg he, Real.norm_of_nonneg (by unfold cuspNorm; positivity)]
    simp only [cuspNorm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← add_mul]
    have hn := norm_sub_le (f (γ • z)) (s * g (γ • z))
    rw [norm_mul] at hn
    exact mul_le_mul_of_nonneg_right hn (by positivity)

/-- The unmodified fresh-prime law used by `moving_of_step`. -/
theorem movingStep {M p : ℕ} (hp : p.Prime) (hodd : Odd p) (h4 : 4 ∣ M)
    (χ : DirichletCharacter ℂ M) (phase : ℂ) {g : ℍ → ℂ}
    (hg : HalfIntegralThreeHalves M χ.toUnitHom g) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    MovingStepLaw M p χ phase g := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h4' := h4.trans (dvd_mul_right M p)
  have hp' := dvd_mul_left p M
  refine ⟨χ.changeLevel (dvd_mul_right M p) * primeCharacter h4' hp', ?_, ?_⟩
  · intro n hn
    rw [MulChar.mul_apply, primeCharacter_nat h4' hp' hodd hn, ← Int.cast_natCast,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hn.isCoprime, Int.cast_natCast]
  · have hV := Vp_threeHalves (p := p) hodd h4 hg
    exact sub_smul_threeHalves (upSquare_threeHalves h4' hp' hodd hV) hV phase

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}

/-- No moving transformation assumption remains for the actual moving series. -/
theorem evenMovingSieve (P : EvenSource W L τ) (hS : SupportSpec W) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) :
    EvenMovingSieveLaw P U := by
  apply moving_of_step P hS U hU
  intro M p hp hodd h4 _ χ g hg
  exact movingStep hp hodd h4 χ (P.phaseData.η p) hg

/-- The fixed weight-two assembly needs only the separate unary transformation
for its analytic inputs. The conclusion retains the intrinsic block characters. -/
theorem evenWeightTwo_from_unary (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (hUnary : ∀ j ∈ subscripts U, EvenUnaryStageLaw P hS i j) :
    ∃ (χB : DirichletCharacter ℂ (movingLevel P U))
      (χJ : ∀ j : ↥(subscripts U), DirichletCharacter ℂ (maskedLevel P * j.val))
      (fB : WeightTwo (movingLevel P U))
      (fJ : ∀ j : ↥(subscripts U), WeightTwo (maskedLevel P * j.val))
      (f : WeightTwo (movingLevel P U)),
      f = assembleForm P U fB fJ ∧
      IsMovingCharacter P U χB ∧ (∀ j, IsUnaryCharacter P i j.val (χJ j)) ∧
      fB ∈ modFormCharSpace 2 χB.toUnitHom ∧
      (∀ j, fJ j ∈ modFormCharSpace 2 (χJ j).toUnitHom) ∧
      (∀ j, includeUnary P U j (fJ j) ∈ modFormCharSpace 2
        ((χJ j).toUnitHom.comp (ZMod.unitsMap (unaryLevel_dvd P U j)))) ∧
      (∀ n, (qExpansion 1 fB).coeff n =
        timesTheta (TL (fun p => P.phaseData.η p) U.toList P.sievedCoeff) n) ∧
      (∀ j n, (qExpansion 1 (fJ j)).coeff n =
        timesTheta (unaryCoeff (evenTypes W.S hS.1).Good (fun p => P.phaseData.η p) i j.val) n) ∧
      ∀ n, (qExpansion 1 f).coeff n =
        timesTheta (halfDivided (evenTypes W.S hS.1).Good
          (fun p => P.phaseData.η p) P.sievedCoeff P.δ i U.toList) n :=
  evenWeightTwo hS i U hU (evenMovingSieve P hS U hU) hodd hUnary

private theorem exists_evenForm (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (hUnary : ∀ j ∈ subscripts U, EvenUnaryStageLaw P hS i j) :
    ∃ f : WeightTwo (movingLevel P U), ∀ n, (qExpansion 1 f).coeff n =
      timesTheta (halfDivided (evenTypes W.S hS.1).Good
        (fun p => P.phaseData.η p) P.sievedCoeff P.δ i U.toList) n := by
  obtain ⟨_, _, _, _, f, _, _, _, _, _, _, _, _, hf⟩ :=
    evenWeightTwo_from_unary hS i U hU hodd hUnary
  exact ⟨f, hf⟩

/-- The form supplied by the fixed even expansion, using only the unary law. -/
def evenForm (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (hUnary : ∀ j ∈ subscripts U, EvenUnaryStageLaw P hS i j) :
    WeightTwo (movingLevel P U) :=
  (exists_evenForm hS i U hU hodd hUnary).choose

variable (hS : SupportSpec W) {B : ℕ} [NeZero (conductor W.S)]
variable {X : Model P hS B} [CharZero X.K] (A : FourierData X) (C : SourceAtPlace P X.O X.K)

/-- Transfer the actual even expansion once the existing constituent
coordinate and unary inputs are supplied. No moving-law premise occurs. -/
theorem evenExpansion_from_unary (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (hUnary : ∀ j ∈ subscripts U, EvenUnaryStageLaw P hS i j)
    (κ : X.K →+* ℂ) (hκ : κ.comp C.eK = C.eC)
    (hcoord : ∀ n, n ≠ 0 → κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
      (qExpansion 1 (evenForm hS i U hU hodd hUnary)).coeff n) :
    ∀ n, n ≠ 0 → A.coeff n (X.F U) = timesTheta (evenH hS A C i U) n :=
  evenExpansion hS A C i U hU _ (exists_evenForm hS i U hU hodd hUnary).choose_spec κ hκ hcoord

end ZInQ.Manuscript.RC.EvenMoving
