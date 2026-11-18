import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ArtinLocal
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Artin34

/-!
# GenusOdd: consistency of `LocalFactorK` and the downstream form of (3.4)

LESSON 2 checks for the GLUE `LocalFactorK` (each clause is a standard local theorem; here we check
that the clauses do not contradict Mathlib's definitions on a genuine example):

* `localFactorK_rat`: the statement of `LocalFactorK` with `K = ℚ` is PROVED (the only prime of `ℚ`
  above `p` is `v` itself, where the local polynomial of `E/ℚ` over `ℚ_v` is computed twice; the
  inert clause is vacuous there);
* `inertShape_consistent` (in `LocalPoly.lean`): the inert clause always has a solution of Mathlib's
  shape (good / multiplicative / additive).

`genusLower34_of_local`: (3.4) from the printed leaves, `HasseConvergence`, `GoodReductionOffLevel`
and `LocalFactorK` (via `genusLower34_of_artin`).
-/

noncomputable section

open NumberField IsDedekindDomain Rat.HeightOneSpectrum

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic

/-- Over `K = ℚ` the two local polynomials agree (PROVED): `E/ℚ` base-changed to `ℚ` is `E`. -/
theorem localPolyK_rat (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    localPolyK (K := ℚ) E v = localPolyQ E v := by
  have h : E.baseChange ℚ = E := by
    simp [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  simp only [localPolyK, localPolyQ, h]
  congr!
  exact Subsingleton.elim _ _

/-- The only prime of `ℚ` above `natGenerator v` is `v` (PROVED). -/
theorem eq_of_mem_primesAbove_rat {v 𝔭 : HeightOneSpectrum (𝓞 ℚ)}
    (h : 𝔭 ∈ primesAbove ℚ (natGenerator v)) : 𝔭 = v := by
  have hdvd : natGenerator 𝔭 ∣ natGenerator v := by
    rw [natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h
    simpa using this
  have heq : natGenerator 𝔭 = natGenerator v :=
    (Nat.prime_dvd_prime_iff_eq (prime_natGenerator 𝔭) (prime_natGenerator v)).mp hdvd
  apply primesEquiv.injective
  exact Subtype.ext heq

/-- **`LocalFactorK` holds for `K = ℚ`** (PROVED; LESSON 2 consistency check of the GLUE on a
genuine example: its first two clauses are the identity there, and its third is vacuous since
`N v = p ≠ p²`). -/
theorem localFactorK_rat (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (𝔭 v : HeightOneSpectrum (𝓞 ℚ)) (h : 𝔭 ∈ primesAbove ℚ (natGenerator v)) :
    (Ideal.absNorm 𝔭.asIdeal = natGenerator v → UnramifiedOver 𝔭 (natGenerator v) →
        localPolyK E 𝔭 = localPolyQ E v) ∧
      (Ideal.absNorm 𝔭.asIdeal = natGenerator v → GoodAt E v →
        localPolyK E 𝔭 = localPolyQ E v) ∧
      (Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2 → UnramifiedOver 𝔭 (natGenerator v) →
        Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
          localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X)) := by
  obtain rfl := eq_of_mem_primesAbove_rat h
  refine ⟨fun _ _ => localPolyK_rat E 𝔭, fun _ _ => localPolyK_rat E 𝔭, fun hN _ => ?_⟩
  exfalso
  have hp := prime_natGenerator 𝔭
  obtain ⟨ℓ, n, hℓ, hn, hNℓ, hmem⟩ := exists_prime_absNorm_eq_pow 𝔭
  -- `N 𝔭 = p`: `ℓ = p` and `n = 1`
  have hℓp : ℓ = natGenerator 𝔭 := by
    have hdvd : natGenerator 𝔭 ∣ ℓ := by
      rw [natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem
      simpa using this
    exact ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp hdvd).symm
  have hN1 : Ideal.absNorm 𝔭.asIdeal = natGenerator 𝔭 := by
    have hfin := finite_quotient 𝔭
    -- `𝓞_ℚ / 𝔭 ≅ ℤ / p`
    have hspan := span_natGenerator 𝔭
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [Nat.card_congr (Ideal.quotientEquiv 𝔭.asIdeal
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) 𝔭.asIdeal)
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) rfl).toEquiv, ← hspan, Nat.card_congr (Int.quotientSpanEquivZMod _).toEquiv, Int.natAbs_natCast,
      Nat.card_zmod]
  rw [hN1] at hN
  have := hp.one_lt
  have : natGenerator 𝔭 < natGenerator 𝔭 ^ 2 := by nlinarith
  omega

/-- **(3.4) from the printed leaves and the local GLUE** (PROVED reduction): `GenusLower34` from
`Prints`, lane RC8's `HasseConvergence`, `GoodReductionOffLevel` and `LocalFactorK`. -/
theorem genusLower34_of_local (P : Prints) (hH : HasseConvergence) (hG : GoodReductionOffLevel)
    (hL : LocalFactorK) : GenusLower34 :=
  genusLower34_of_artin P (artinFactorization_of_local hH hG hL)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
