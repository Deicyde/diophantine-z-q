import ZInQKernel.Contrib.GZTheta.BadCoeff
import ZInQKernel.Contrib.GZTheta.EtaForm32

/-!
# gz-theta: main reductions of the leaf `HeckeThetaNewform`

* `EtaThetaIdentity`: the classical `q`-series identity
  `η(4τ)² η(8τ)² = ∑_{n ≥ 1} heckeCoeff 1 n qⁿ = ∑_{α ≡ 1 mod (2+2i)} α q^{N α}`.
  Not proved here (a consequence of Jacobi's triple product; VERIFIED numerically for `n ≤ 400`).
* `cmForm32_of_etaThetaIdentity : EtaThetaIdentity → CMForm32`, from the cusp form
  `etaForm32 ∈ S₂(Γ₀(32))` (proved: `Eta32.lean`, `EtaForm32.lean`).
* The leaf from `EtaThetaIdentity` and newness (`NewCM`), or the bad coefficients (`BadCoeffCM`).
-/

open Complex ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE

/-- **The `q`-expansion of `η(4τ)² η(8τ)²`**: for `τ` in the upper half-plane,
`η(4τ)² η(8τ)² = ∑_{n ≥ 0} heckeCoeff 1 n · e^{2π i n τ}`, i.e.
`q ∏_{n ≥ 1} (1 − q^{4n})² (1 − q^{8n})² = ∑_{α ∈ ℤ[i], α ≡ 1 mod (2+2i)} α q^{N α}`.
Classical (Jacobi's identity `η(8τ)³ = ∑_{a ≡ 1 (4)} a q^{a²}` times Gauss's
`η(4τ)²/η(8τ) = ∑_m (−1)^m q^{4m²}`, both from the triple product identity; UNVERIFIED locator:
Köhler, *Eta products and theta series identities* (2011)). VERIFIED numerically for `n ≤ 400`
(`scratch/gz-theta/qexp_check.py`). Not proved here. -/
def EtaThetaIdentity : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => heckeCoeff 1 n * cexp (2 * π * I * τ) ^ n)
    (η (4 * (τ : ℂ)) ^ 2 * η (8 * (τ : ℂ)) ^ 2)

theorem one_mem_strictPeriods_Gamma0_map (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N).map (mapGL ℝ)).strictPeriods := by
  simp [CongruenceSubgroup.strictPeriods_Gamma0]

/-- **`CMForm32` from the `q`-series identity**: `etaForm32` is the required cusp form. -/
theorem cmForm32_of_etaThetaIdentity (h : EtaThetaIdentity) : CMForm32 := by
  refine ⟨etaForm32, fun n => ?_⟩
  have key : ∀ τ : ℍ, HasSum (fun m : ℕ => heckeCoeff 1 m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (etaForm32 τ) := by
    intro τ
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = cexp (2 * π * I * τ) := by
      simp [Function.Periodic.qParam]
    simpa [hq, smul_eq_mul, coe_etaForm32, etaQuot32] using h τ
  exact (ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma0_map 32) key n).symm

/-- **The leaf from the `q`-series identity and newness.** -/
theorem heckeThetaNewform_of_etaThetaIdentity_newCM (h : EtaThetaIdentity) (hnew : NewCM) :
    ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_cmForm32_newCM (cmForm32_of_etaThetaIdentity h) hnew

/-- **The leaf from the `q`-series identity and the bad-prime coefficients.** -/
theorem heckeThetaNewform_of_etaThetaIdentity_badCoeffCM (h : EtaThetaIdentity)
    (hbad : BadCoeffCM) : ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_cmForm32_badCoeffCM (cmForm32_of_etaThetaIdentity h) hbad

end ZInQ.GZTheta
