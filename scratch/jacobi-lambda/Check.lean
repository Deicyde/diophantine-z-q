import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.JacobiLambdaDeriv

/-! jacobi-lambda statement and axiom check.
The target Prop is copied verbatim (with its three definitions) from gz-weil's `WeilTheta.lean`
(f4a06a48) into the namespace `JLCopy`, and checked against gz-weil's constant by `Iff.rfl`. -/

open Complex
open scoped Real

noncomputable section

namespace JLCopy

/-- `θ₂(t) = Σ_{n ∈ ℤ} e^{πi(n + 1/2)² t}`. -/
def thetaTwo (t : ℂ) : ℂ := cexp (π * I * t / 4) * jacobiTheta₂ (t / 2) t

/-- `θ₃(t) = Σ_{n ∈ ℤ} e^{πin² t}`. -/
def thetaThree (t : ℂ) : ℂ := jacobiTheta₂ 0 t

/-- `θ₄(t) = Σ_{n ∈ ℤ} (−1)ⁿ e^{πin² t}`. -/
def thetaFour (t : ℂ) : ℂ := jacobiTheta₂ (1 / 2) t

def JacobiLambdaDeriv : Prop :=
  ∀ t : ℂ, 0 < t.im → HasDerivAt (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4)
    (π * I * (thetaTwo t ^ 4 / thetaThree t ^ 4) * thetaFour t ^ 4) t

theorem copy_iff : JacobiLambdaDeriv ↔ ZInQ.GZWeil.JacobiLambdaDeriv := Iff.rfl

theorem copy_proved : JacobiLambdaDeriv := copy_iff.mpr ZInQ.GZWeil.jacobiLambdaDeriv

end JLCopy

#check (ZInQ.GZWeil.jacobiLambdaDeriv : ZInQ.GZWeil.JacobiLambdaDeriv)
#print axioms ZInQ.GZWeil.jacobiLambdaDeriv
#print axioms JLCopy.copy_proved
#print axioms ZInQ.GZWeil.etaModelDifferential
#print axioms ZInQ.GZWeil.modularParamC1
#print axioms ZInQ.GZWeil.shimuraCMParamCd
#print axioms ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves4
