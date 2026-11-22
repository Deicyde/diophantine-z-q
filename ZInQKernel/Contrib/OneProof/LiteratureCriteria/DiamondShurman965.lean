import ZInQKernel.Contrib.OneProof.LiteratureCriteria.DS965ResidueAction

/-! # Diamond–Shurman Theorem 9.6.5 in the algebraic-integer prime convention -/

namespace DS965Places

open NumberField IsDedekindDomain DSCoeffExt
open ZInQ.Contrib.G9.PkgI4 (Qbar GQ CF coeff)
open ZInQ.Contrib.ChebFD.C10 (Zbar)
open ZInQ.Contrib.ChebFD.HSyn (gZ)
open Polynomial (X C)
open scoped NumberField

/-- Diamond–Shurman, *A First Course in Modular Forms*, Springer GTM 228 (2005),
Thm. 9.6.5, p. 404 of the corrected fourth printing (2016), omitting the unused
irreducibility conclusion. The hypothesis `2 ≤ k` is this project's restriction, not a
hypothesis of the print, which has no weight bound.
Normalized eigenforms are as in Def. 5.8.1. The unramified and arithmetic
Frobenius clauses use reduction at primes of the algebraic integers as in
§9.3. We write the polynomial with a coefficient `b` equal to `χ(p) p^(k-1)`
in the embedded coefficient field. Kind: PRINT, restricted form. -/
def DiamondShurman965AtPrimes : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    2 ≤ k → IsNormalizedEigenformDS f χ → ∀ [NumberField (coeffField f)]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (coeffField f))),
    (ℓ : 𝓞 (coeffField f)) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (coeffField f)), Continuous ρ ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        ∀ P : Ideal Zbar, P.IsMaximal → P.under ℤ = Ideal.span {(p : ℤ)} →
          (∀ σ : GQ, (∀ x : Zbar, gZ σ x ∈ P ↔ x ∈ P) →
            (∀ x : Zbar, gZ σ x - x ∈ P) → ρ σ = 1) ∧
          ∀ b : coeffField f, (b : ℂ) = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) →
          ∀ σ : GQ, (∀ x : Zbar, gZ σ x ∈ P ↔ x ∈ P) →
            (∀ x : Zbar, gZ σ x - x ^ p ∈ P) →
            (ρ σ : Matrix (Fin 2) (Fin 2) (lam.adicCompletion (coeffField f))).charpoly =
              X ^ 2 - C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                ⟨coeff f p, coeff_mem_coeffField f p⟩) * X +
                C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) b)

/-- The precise live row follows from the book's prime-ideal formulation.
No change of representation, choice of basis or inversion of Frobenius occurs. -/
theorem dsThm965Printed_of_atPrimes (h : DiamondShurman965AtPrimes) : DSThm965Printed := by
  apply dsThm965Printed_of_charpoly
  intro N _ k χ f hk hf _ ℓ _ lam hlam
  obtain ⟨ρ, hc, hρ⟩ := h N k χ f hk hf ℓ lam hlam
  refine ⟨ρ, hc, fun p hp hgood => ⟨?_, ?_⟩⟩
  · intro v hv σ hσ
    have hI := inertia_congr v σ hσ
    have hS := stabilizes_of_congr (placeIdeal v) σ.val 1 (by decide)
      (fun x => by simpa only [pow_one] using hI x)
    exact (hρ p hp hgood (placeIdeal v) (placeIdeal_isMaximal v hp hv)
      (placeIdeal_under v hp hv)).1 σ.val hS hI
  · intro b hb v σ hv hσ
    have hF := frobenius_congr v p σ hσ
    have hS := stabilizes_of_congr (placeIdeal v) σ p hp.ne_zero hF
    exact (hρ p hp hgood (placeIdeal v) (placeIdeal_isMaximal v hp hv)
      (placeIdeal_under v hp hv)).2 b hb σ hS hF

end DS965Places
