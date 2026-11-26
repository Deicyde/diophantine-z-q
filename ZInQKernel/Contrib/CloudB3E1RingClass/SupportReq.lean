import ZInQKernel.Contrib.CloudB3E2Norm.E2ChainGood
import ZInQKernel.Contrib.CloudB3E1RingClass.CurveData
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Curve

/-!
# The support requirements `hS2N` and `h3ℓ`

Manuscript `diophantine_zq.tex`, tex 2678–2680, 2729–2741 ("the fixed support contains the primes
of `2N`"), 4234–4237.

Lane E2's chain-input constructors (`e2ChainInputsS_of_actual`, `e2ChainInputsS_of_actual'`) name
two formalization requirements:
* `hS2N`: the primes of `2N` lie in the fixed support `D.S`, `N = newformLevel E_ℓ`;
* `h3ℓ`: the places above `3ℓ` lie in the stage support `S₀ (t + 1)`.

This file reduces both to statements about the base support `S0 ℓ = {2, 3} ∪ primes(ℓ)` (the
`PreDataSpec.support_base` requirement):

* **`LevelPrimesBad`** (named input; GLUE, uncited by the text): a prime dividing the level of the
  newform of `E` is a prime at which no model of `E` is good. Equivalently, good reduction at `p`
  forces `p ∤ N`. This is H. Carayol, *Sur les représentations ℓ-adiques associées aux formes
  modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986), Théorème (A) (the level of the newform is the
  conductor `N_E`), with the definition of the conductor (its exponent at `p` is `0` exactly when
  `E` has good reduction at `p`). It is the converse of the tree's proved
  `GoodReductionOffLevel`. The tree's `newformLevel` is the least level of a cusp form with the
  coefficients of `L(E, s)`, and no conductor computation is formalized. In the tree's eigenform
  structure the newform carries Hecke eigenvalues only at the good indices, so `U_p` at `p ∣ N` is
  not available to derive it.
* **`hS2N_of_levelPrimesBad`** (PROVED): `hS2N` from `LevelPrimesBad` and `S0 ℓ ⊆ D.S`. A prime of
  `N` is bad for the model `y² = x(x − ℓ)(x + 3ℓ)`, so it divides `6ℓ` (`bad_curve_mem`).
* **`h3ℓ_of_support`** (PROVED): `h3ℓ` from `S0 ℓ ⊆ D.S` and the requirement that the stage support
  contain the places above `D.S`. The text's coefficient support contains the fixed support; the
  places above `3ℓ` lie above `3` or a prime of `ℓ`, both in `S0 ℓ`.
* `ell_ne_zero` (PROVED): `E_ℓ` elliptic forces `ℓ ≠ 0`.
* **`e2ChainInputsS_of_support`** (definition): lane E2's chain inputs with `hS2N` and `h3ℓ`
  replaced by `LevelPrimesBad`, `S0 ℓ ⊆ D.S` and `hS₀D`.

What remains named: `LevelPrimesBad` (GLUE, Carayol); `S0 ℓ ⊆ D.S` (`RCData` does not record the
base support; it is `PreDataSpec.support_base` for the support the data are built from); and
`hS₀D` (the places above `D.S` lie in `P.S₀ (t + 1)`). The last is not implied by the staged
presentation, because `StagedPresentation.S₀` is free data constrained only by `hSr`, `full` and
`Cc`. It is the text's "the coefficient support contains the fixed support" (tex 2729–2741).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.PrintsArith (Qbar CCLThm2_15AppliedWithUnits)
open ZInQ.Contrib.CloudB3E2.NormCochain (CSTParam FullAnchor)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)
open ZInQ.Manuscript.RC.Nonvanishing (GoodAt bad_curve_mem)

/-- **A prime of the level of the newform of `E` is bad for every model of `E`** (named input;
PRINT + GLUE): Carayol 1986 (bibitem `carayol`), §0.8, Corollaire, p. 411 (page-checked): "Soit
f ∈ S₂(Γ₀(N)) une nouvelle forme rationnelle, valeur propre normalisée des opérateurs de Hecke, et
soit E_f la courbe elliptique sur Q associée à f. Alors la fonction L de E_f est égale à L(f, s),
et le conducteur géométrique de E_f est égal à N." (Théorème (A) itself is on pp. 410–411.)
GLUE: modularity (BCDT) gives `E` isogenous to `E_f` with `f` of level `newformLevel E`; the
conductor is an isogeny invariant, and its exponent vanishes exactly at the primes of good
reduction. Stated for the tree's `newformLevel` and `Nonvanishing.GoodAt` (the given model is good
at `p`, which implies good reduction). It includes modularity (BCDT): for a non-modular `E` the
tree's `newformLevel E` would be `0`. Kind: definition (named input).
Links: Carayol 1986 https://www.numdam.org/item/ASENS_1986_4_19_3_409_0/;
Breuil–Conrad–Diamond–Taylor https://virtualmath1.stanford.edu/~conrad/papers/tswfinal.pdf. -/
def LevelPrimesBad : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ p : ℕ, p.Prime → p ∣ newformLevel E → ¬ GoodAt E p

/-- `E_ℓ` elliptic forces `ℓ ≠ 0` (PROVED). -/
theorem ell_ne_zero {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] : ℓ ≠ 0 := by
  rintro rfl
  have h := (Ecurve 0).isUnit_Δ
  rw [ZInQ.Contrib.CloudB3E2.ChainActual.ecurve_eq, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_Δ, ZInQ.Contrib.CloudB3E2.ChainActual.intCurve_Δ] at h
  simp at h

/-- **`hS2N` from `LevelPrimesBad` and the base support** (PROVED; tex 2678–2680, 2729–2741). -/
theorem hS2N_of_levelPrimesBad (hlev : LevelPrimesBad) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    {S : Finset ℕ} (hbase : S0 ℓ ⊆ S) :
    ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S := by
  have hℓ : ℓ ≠ 0 := ell_ne_zero
  have h2 : 2 ∈ S := hbase (by simp [S0])
  have h3 : 3 ∈ S := hbase (by simp [S0])
  intro p hp hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h]
    exact h2
  · have hbad := hlev _ inferInstance p hp h
    have hm : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (ℓ : ℤ) → q ∈ S := by
      intro q hq hqd
      apply hbase
      have : q ∣ ℓ := by exact_mod_cast hqd
      simp [S0, Nat.mem_primeFactors, hq, this, hℓ]
    refine bad_curve_mem (m := (ℓ : ℤ)) h2 h3 hm p hp ?_
    simpa [Ecurve] using hbad

/-- **`h3ℓ` from the base support and the stage support** (PROVED; tex 2729–2741): if the stage
support contains the places above the fixed support `S ⊇ S0 ℓ`, it contains the places above
`3ℓ`. -/
theorem h3ℓ_of_support {K : Type} [Field K] [NumberField K] {ℓ : ℕ} (hℓ : ℓ ≠ 0) {S : Finset ℕ}
    (hbase : S0 ℓ ⊆ S) {S₀ : Set (HeightOneSpectrum (𝓞 K))}
    (hS₀ : ∀ p ∈ S, ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ v : HeightOneSpectrum (𝓞 K), ((3 * ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₀ := by
  intro v hv
  obtain ⟨p, hp, hpd, hpv⟩ := exists_prime_dvd_of_mem v (by positivity) hv
  refine hS₀ p (hbase ?_) v hpv
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h]
    simp [S0]
  · simp [S0, Nat.mem_primeFactors, hp, h, hℓ]

section Chain

open ZInQ.Contrib.CloudB3E2.ChainActual

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}

attribute [local instance] ZInQ.Manuscript.RC.CoefModules.acoefTop
  ZInQ.Manuscript.RC.CoefModules.acoefTop_discrete ZInQ.Contrib.CloudB3E2.NormCochain.stageIsoA

/-- **Lane E2's chain inputs with the support requirements reduced** (tex 2678–2680,
2729–2741): as `e2ChainInputsS_of_actual'`, with `hS2N` from `LevelPrimesBad` and `S0 ℓ ⊆ D.S`,
and `h3ℓ` from `S0 ℓ ⊆ D.S` and `hS₀D` (the stage support contains the places above `D.S`).
Kind: definition. -/
def e2ChainInputsS_of_support (P : StagedPresentation C D Fam x G.toFamily) (t : ℕ)
    (cp : CSTParam (Ecurve ℓ)) (emb : Qbar →ₐ[ℚ] ℂ) (κ : Qbar ≃ₐ[ℚ] AlgebraicClosure C.K)
    (print : CCLThm2_15AppliedWithUnits (Ecurve ℓ) C.K (FullAnchor (Ecurve ℓ) C.K cp emb κ))
    (St : RCSteps D) (hodd : ¬ D.OddEmptyUnit) (hAdm : Fam.Admissible D.S D.kfin)
    (hlev : LevelPrimesBad) (hbase : S0 ℓ ⊆ D.S)
    (hS₀D : ∀ p ∈ D.S, ∀ v : HeightOneSpectrum (𝓞 C.K), ((p : ℕ) : 𝓞 C.K) ∈ v.asIdeal →
      v ∈ P.S₀ (t + 1))
    (hrk : ¬ ((G.r (t + 1) : ℕ) : ℤ) ∣ D.kfin)
    (hQS0 : ∀ q ∈ Fam.Q, Fam.lam q x = 1 → ∀ v : HeightOneSpectrum (𝓞 C.K),
      ((q : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S₀ (t + 1))
    (hpidx : ∀ p : P.ι, ∃ j < P.ps.length, P.pidx j = p) (hQ3 : ∀ q ∈ unusedAt Fam x, q ≠ 3) :
    E2ChainInputsS P t :=
  e2ChainInputsS_of_actual' P t cp emb κ print St hodd hAdm (hS2N_of_levelPrimesBad hlev hbase)
    hrk hQS0 hpidx hQ3 (h3ℓ_of_support ell_ne_zero hbase hS₀D)

end Chain

end ZInQ.Contrib.CloudB3E1RingClass
