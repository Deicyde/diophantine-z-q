/-
POSITIVE necessity controls for S1 (must COMPILE).
They prove that the two shape hypotheses of S1 cannot be dropped:
  * the scalar must be NONZERO (`le_comap_smul_iff`),
  * the twist must be by a SCALAR, not by an invertible operator.
-/
import S1Twist

namespace ScaledS1Neg

/-- **The nonzero hypothesis is necessary.** With `χ = 0` the implication
`W ≤ W.comap (χ • f) → W ≤ W.comap f` fails. -/
theorem zero_twist_not_reflected :
    ∃ (W : Submodule ℚ (ℚ × ℚ)) (f : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)),
      W ≤ W.comap ((0 : ℚ) • f) ∧ ¬ (W ≤ W.comap f) := by
  refine ⟨LinearMap.ker (LinearMap.snd ℚ ℚ ℚ), (LinearEquiv.prodComm ℚ ℚ ℚ).toLinearMap, ?_, ?_⟩
  · intro v _
    simp
  · intro h
    have h1 : ((1 : ℚ), (0 : ℚ)) ∈ LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) := by simp
    have := h h1
    simp [LinearMap.mem_ker] at this

/-- **The twist must be by a scalar.** A twist by an invertible operator changes the
invariant-subspace lattice: here `W` is invariant under `u ∘ f` (the identity) but not under
`f` (the swap), with `u = f` invertible. So the S1 route genuinely needs `μ_σ` scalar on `G_L`,
not merely a unit. -/
theorem unit_twist_not_reflected :
    ∃ (W : Submodule ℚ (ℚ × ℚ)) (u f : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)),
      Function.Bijective u ∧ W ≤ W.comap (u ∘ₗ f) ∧ ¬ (W ≤ W.comap f) := by
  classical
  refine ⟨LinearMap.ker (LinearMap.snd ℚ ℚ ℚ), (LinearEquiv.prodComm ℚ ℚ ℚ).toLinearMap,
    (LinearEquiv.prodComm ℚ ℚ ℚ).toLinearMap, (LinearEquiv.prodComm ℚ ℚ ℚ).bijective, ?_, ?_⟩
  · intro v hv
    simpa using hv
  · intro h
    have h1 : ((1 : ℚ), (0 : ℚ)) ∈ LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) := by simp
    have := h h1
    simp [LinearMap.mem_ker] at this

end ScaledS1Neg
