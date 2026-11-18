import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceCorrelationForms

/-!
# Lower product-span forms for determinant orbit sums

The actual finite Fourier reduction constructs a lower modular form from
verified signed correlation forms. Its membership is in the genuine Good
principal-product span, with no full-space spanning assertion.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation TorsionQuadraticGenerators

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The lower actual form supplied by the determinant-pair Fourier reduction. -/
def determinantOrbitForm (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (d : ZMod p) (A B : Point N) : _root_.ModularForm (ΓP N) 2 := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  exact -(1 / (N : ℂ)) • ∑ C : Point N, pairing N (scale (p : ZMod N) C) B •
    ∑ s : ZMod p, phase p (-(N : ZMod p) * d * s) • nonzeroCorrelationForm p N hN s A C

/-- Evaluation is exactly the actual determinant orbit sum. -/
theorem determinantOrbitForm_apply (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (hcop : Nat.Coprime p N) (d : ZMod p) (A B : Point N) (τ : ℍ) :
    determinantOrbitForm p N hN d A B τ = determinantOrbitValue p N τ d A B := by
  let : NeZero N := ⟨hN.ne'⟩
  unfold determinantOrbitForm
  simp only [smul_apply, smul_eq_mul, sum_apply, nonzeroCorrelationForm_apply]
  exact (actual_determinant_orbit_reduction p N hcop τ d A B).symm

/-- The independently constructed lower determinant orbit form is in the
actual Good degree-two principal-product span. -/
theorem determinantOrbitForm_mem_productSpan (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (h3 : 3 ≤ N) (d : ZMod p) (A B : Point N) :
    determinantOrbitForm p N hN d A B ∈ productSpan N hN := by
  classical
  unfold determinantOrbitForm
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro C _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro s _
  apply Submodule.smul_mem
  exact nonzeroCorrelationForm_mem_productSpan p N hN h3 s A C

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
