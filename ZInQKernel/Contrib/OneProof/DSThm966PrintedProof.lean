import ZInQKernel.Contrib.OneProof.DSThm966EV
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.PrintedBridge
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.BridgeLemmas
import ZInQKernel.Contrib.CloudB3SC5FiniteImage.ContinuousFiniteImage
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen

/-!
# Weight-one Deligne–Serre, printed form — contribution entry point

`dsThm966Printed : DSThm966EV.DSThm966Printed`.

Chain:
1. The vendored Anthropic FLT theorem
   `P2MW.S_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen.solution`
   (upstream statement without its irreducibility conjunct, which is not used here) gives, for a weight-one
   cusp form on `Γ₁(N)` with `a₁ = 1` and the prime Hecke recurrence, a homomorphism
   `ρ : Gal(ℚ̄/ℚ) →* GL₂(ℂ)` trivial on `Gal(ℚ̄/L)` for a finite `L/ℚ`, unramified at every `p ∤ N`, with
   Frobenius trace `a_p` and determinant `χ(p)`.
2. `CloudB3SC5DeligneSerre.BridgeLemmas`: the recurrence holds for a pkg-I4 normalized eigenform; the
   finite-level condition gives Krull continuity; places, inertia and Frobenius convert to pkg-I4's.
3. `CloudB3SC5FiniteImage`: a continuous `G_ℚ → GL₂(ℂ)` has finite range.
   Together: `ZInQ.Contrib.HodgeSplit.DSThm966` (`dsThm966_proof` below).
4. `CloudB3SC5DeligneSerre.PrintedBridge.dsThm966Printed_of_dsThm966` gives the printed form.

No new premise, axiom or copy of the target is introduced.
-/

namespace ZInQ.Contrib.CloudB3SC5DeligneSerre

open ZInQ.Contrib.G9

/-- `ZInQ.Contrib.HodgeSplit.DSThm966`, from the vendored weight-one Deligne–Serre theorem. -/
theorem dsThm966_proof : ZInQ.Contrib.HodgeSplit.DSThm966 := by
  intro N χ g hN hg
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ρ, hfl, hρ⟩ :=
    P2MW.S_DeligneSerre_exists_galoisRep_of_weightOne_qCoeff_hecke_eigen.solution N χ g hg.2.1
      (fun p hp _ n => coeff_prime_mul_add_of_isNormalizedEigenform χ g hg hp n)
  have hcont : Continuous ρ := continuous_of_exists_finiteLevel ρ hfl
  refine ⟨ρ, hcont, ZInQ.Contrib.CloudB3SC5FiniteImage.finite_range_of_continuous_galQbar ρ hcont,
    fun p hp hpN => ⟨?_, ?_⟩⟩
  · intro v hv σ hσ
    exact (hρ p hp hpN v ((liesOverPrime_iff_liesOver v p).mpr hv)).1 _
      (mem_inertiaSubgroupIn_of_mem_inertiaSubgroup hσ)
  · intro v σ hv hσ
    exact (hρ p hp hpN v ((liesOverPrime_iff_liesOver v p).mpr hv)).2 σ
      (isFrobeniusAt_of_isArithFrob hσ)

/-- **Weight-one Deligne–Serre, printed form** (`DSThm966EV.DSThm966Printed`). -/
theorem dsThm966Printed : DSThm966EV.DSThm966Printed :=
  dsThm966Printed_of_dsThm966 dsThm966_proof

end ZInQ.Contrib.CloudB3SC5DeligneSerre
