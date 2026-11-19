import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Realization
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitCertificate

/-!
# The nonquadratic switch step from retained stage data

The fixed-`P` nonquadratic step of the inner limit is assembled from the two producers of its
inputs: the switching duality of the retained limit diagram from the retained stage pairing and
global duality data with the transported local pairing at the derivative label, and the
rank-two detection from a degree-one realization of the same limit diagram at the moving label.
The duality, the detection and the conjugation all refer to one retained diagram: the global
limit model `C` and its retained localization `D.resLimit`.

Sources: the retained inner limit, manuscript lines 4391–4451; the derivative-condition lemma,
lines 4834–4907; height-one regularity, lines 4976–5135.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitArith

open Filter NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS Gloc urRes)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (selCx)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped PowerSeries.WithPiTopology

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} {α : GKS K S →* Lambdaˣ} [W.IsElliptic] [HasFullTwoTorsion K S W]
  [IsContChar α]

/-- **The nonquadratic switch step of the retained limit diagram**: the switching duality from the
retained stage pairing and global duality data (`D`, `E`) with the transported local pairing
(`hloc`, `J = ρ_T(τ)`), the rank-two detection from a degree-one realization of the same limit
diagram at the moving label (two global cycles whose stage cocycles have independent limit
Frobenius values), and the two side-to-stage equivalences. -/
def retainedNonquadStep (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] (C : ComplexStages (R := Lambda) stageIdeal U)
    {D : RetainedLimitPairingStages U C} (E : RetainedGlobalDualityStages D)
    (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W)
    (ε₀ ε₂ ε σ : ResAt P) (hε₂ : ε₂ ≠ 0) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hloc : localPairingOfMat (D.locK P) =
      transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P))
    (L : MovingLabel K S) (σl : ∀ i, Gloc K (L.q i)) (hσl : ∀ i, urRes K (L.q i) (σl i) = 1)
    (R : DegreeOneRealization W α P (fibreLimitGlobal U hU P C) (D.resLimit hU P) L σl U)
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} (S₀ S₁ : TwoTermStage ι)
    (a b : LinearMap.ker ((fibreLimitGlobal U hU P C).d 1 2 rfl))
    (hdet : (Matrix.of ![limitFrobValue P L U (R.cocycle a),
      limitFrobValue P L U (R.cocycle b)]).det ≠ 0)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) S₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) S₁) :
    QuasiNonquadStep (resAt P) S₀ S₁ :=
  realizedFibreLimitNonquadStep U hU P C (D.resLimit hU P) L σl hσl R S₀ S₁ ε σ
    (conjMatrix Cn W hW P) hε hσ (conjMatrix_mul_self Cn W hW P)
    (fibreInnerLimitDuality_of_retained hU E P Cn W hW ε₀ ε₂ ε σ hε₂ hε hσ hloc) a b hdet φ φ'

/-- The step drops the stage fibre dimension by two. -/
theorem retainedNonquadStep_drop (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] (C : ComplexStages (R := Lambda) stageIdeal U)
    {D : RetainedLimitPairingStages U C} (E : RetainedGlobalDualityStages D)
    (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W)
    (ε₀ ε₂ ε σ : ResAt P) (hε₂ : ε₂ ≠ 0) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hloc : localPairingOfMat (D.locK P) =
      transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P))
    (L : MovingLabel K S) (σl : ∀ i, Gloc K (L.q i)) (hσl : ∀ i, urRes K (L.q i) (σl i) = 1)
    (R : DegreeOneRealization W α P (fibreLimitGlobal U hU P C) (D.resLimit hU P) L σl U)
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} (S₀ S₁ : TwoTermStage ι)
    (a b : LinearMap.ker ((fibreLimitGlobal U hU P C).d 1 2 rfl))
    (hdet : (Matrix.of ![limitFrobValue P L U (R.cocycle a),
      limitFrobValue P L U (R.cocycle b)]).det ≠ 0)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) S₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) S₁) :
    S₁.fiberDim (resAt P) + 2 = S₀.fiberDim (resAt P) :=
  (retainedNonquadStep U hU P C E Cn hW ε₀ ε₂ ε σ hε₂ hε hσ hloc L σl hσl R S₀ S₁ a b hdet φ
    φ').toNonquadDims.drop

end ZInQ.Contrib.RC53Assist.InnerLimitArith
