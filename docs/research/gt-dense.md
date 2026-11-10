# Green–Tao, dense form, from the Ilin Lean proof: plan

Task `gt-dense-plan`, 2026-11-09. Log: `scratch/gt-dense-plan/log.md`.

Goal: a Lean proof of `ZInQ.GreenTaoDense` (`ZInQKernel/Hypotheses/GreenTao.lean`):

```lean
def GreenTaoDense : Prop :=
  ∀ A : Set ℕ, A ⊆ {p | p.Prime} → PrimesRelUpperDensityPos A → ContainsArbitraryAPs A
```

built from Vasily Ilin's Lean proof of Green–Tao Theorem 1.1 (`Vilin97/Autoformalization`,
`green-tao/`, commit `0dc67d87416c19690dd641a178ada32cca95c651`, Apache-2.0), with as little new code
as possible. Task `gt-import` vendors that development, unmodified, under `ThirdParty/GreenTao/`
(lean_lib `GreenTaoVendor`, module names `Submission.*`). File references `Submission/...:N` below
are to the source at that commit. The vendored copy is byte-identical, so the line numbers hold
there too.

## Summary

1. **Answer to question 2: relative counting is general.** The transference theorem
   `relativeAPCount_lower_bound_of_linearFormsCondition` (`Submission/Transference/RelativeSzemeredi.lean:114`)
   holds for any `f : ZMod N → ℝ` with `0 ≤ f ≤ ν`. Its comparison hypothesis `RelativeAPComparisonLe`
   (`:40`) quantifies over all such `f`. Ordered removal, relative counting and the linear-forms estimate
   for the majorant never mention the prime indicator. Nothing in the deep part has to be generalized.
2. **The primes enter in only three places:**
   - the definition of the weight `wTrickedPrimeWeight` (`Submission/Primes/WTrick.lean:46`);
   - the Chebyshev lower bound on the number of primes in `(X/4, X]` at every large `X`, used by the
     density pigeonhole (`Submission/Primes/WTrickDensity.lean`, `Submission/Primes/Chebyshev.lean`);
   - the two ends of the proof: extraction (positive weight implies prime,
     `Submission/Primes/Extraction.lean:17`) and lengths `k ≤ 2` (`2, 3`,
     `Submission/Primes/SmallProgressions.lean`).

   The majorization `wTrickedPrimeWeight ≤ ν` (`Submission/GreenTao/Majorization.lean:331`) is a
   statement about the prime weight. For `A` it is inherited from the pointwise bound
   `1_A · weight ≤ weight`.
3. **One step has a different shape, not just a different weight.** For the set of primes, the density
   bound holds at *every* large cyclic modulus. So the assembly lets the transference pick the prime
   modulus (`∀ M₀, ∃ M ≥ M₀, Nat.Prime (M+1) ∧ …`). For a set `A` of positive *upper* density the bound
   holds only along a sequence of scales, and only in *some* window `(Z/2, Z]`, not necessarily in the
   fixed window `(X/4, X]` that the W-trick samples. The A-version therefore needs three changes:
   - the transference stated for **every** large prime modulus. The existing proof already shows this,
     but the existing predicate only exposes an existential.
   - a dyadic **window lemma** that turns `PrimesRelUpperDensityPos A` into frequent mass in a window
     of ratio 2. This needs Chebyshev's upper bound `π(Y) ≪ Y / log Y`, which the original proof never
     uses.
   - a **Bertrand modulus selection**: a prime modulus `q` with `W·⌊q/8⌋ ∈ [Z, 3Z]`, so that the
     sampled window contains most of `(Z/2, Z]`.
4. **Size.** No vendored file has to change. All new code goes into new files that import the vendored
   modules: about 700–900 lines in about 7 files. About 350 of those lines are adapted copies of
   vendored proofs, which carry Apache modification notices. The rest is new elementary analysis (the
   window lemma) and glue.

## 1. Where the set of primes enters

### 1.1 The assembly chain, top down

`Submission.lean:8`:

```lean
theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  refine
    GreenTao.containsArbitraryAPs_primes_of_orderedRemoval_of_linearForms
      ?_ GreenTao.hasStandardCyclicMajorantLinearForms
  intro k hk
  ...
  exact GreenTao.hasUniformOrderedPatternRemoval_sourceFull k (k - 2) (by omega)
```

| level | declaration | file:line | mentions primes? |
|---|---|---|---|
| 0 | `containsArbitraryAPs_primes_of_orderedRemoval_of_linearForms` | `GreenTao/FinalTransferenceAssembly.lean:188` | conclusion only |
| 1 | `hasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts_of_orderedRemoval_of_linearForms` | `GreenTao/FinalTransferenceAssembly.lean:56` | through `wTrickedPrimeWeight` and the fixed `densityTarget` |
| 2 | `cofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount_of_eventually` | `GreenTao/ReducedResidueCofinalTransference.lean:55` | through `wTrickedPrimeWeight` only (as `f`) |
| 3 | `containsArbitraryAPs_primes_of_standard_reducedResidue_cofinal_prime_counts` and `….toCountLower` | `GreenTao/ReducedResidueCofinalTransference.lean:212, 177` | yes: density selection |
| 4 | `HasCofinalPrimeWTrickedPrimeProgressionCountLower.toMass` | `GreenTao/CofinalPrimeModulusAssembly.lean:77` | weight height bound |
| 5 | `containsArbitraryAPs_primes_of_mass` | `GreenTao/Assembly.lean:56` | yes: extraction and `k ≤ 2` |

(Paths are relative to `Submission/`.) `AsymptoticAssembly.lean`, `CofinalPrimeTransference.lean:81`
and the rest of `CofinalPrimeModulusAssembly.lean` hold older interfaces and compatibility theorems.
They are not on the path of `green_tao`, except for the uniform majorization lemma
`eventually_all_residues_wTrickedPrimeWeight_le_cyclicMajorant` (`GreenTao/CofinalPrimeTransference.lean:31`).

### 1.2 The prime-specific definitions and theorems

**The weight** (`Primes/WTrick.lean:19, 46`):

```lean
def greenTaoInterval (N : ℕ) : Finset ℕ := Finset.Icc (N / 64) (N / 4)

noncomputable def wTrickedPrimeWeight {N : ℕ} [NeZero N]
    (α : ℝ) (W b : ℕ) (n : ZMod N) : ℝ :=
  if n.val ∈ greenTaoInterval N ∧ Nat.Prime (wTrickedValue W b n) then
    α * ((W.totient : ℝ) / W) * Real.log (wTrickedValue W b n)
  else 0
```

where `wTrickedValue W b n = W * n.val + b`. The scale `α = primeScale k normalizer`
(`GreenTao/Parameters.lean:39`) is capped so that the weight stays below the Selberg majorant. It
cannot be raised to make up for a small density.

**Density selection** (`Primes/WTrickDensity.lean`, `Primes/Chebyshev.lean`). The sampling scale is
`X = wTrickPrimeScale W N = W * (N / 8)` (`WTrickDensity.lean:22`). The sampled primes are those in
`(X/4, X]` with residue `b` mod `W` (`quarterIntervalResidueClass`, `:27`). The chain is:

```lean
-- Primes/Chebyshev.lean:214   (all primes; eventually in X)
theorem eventually_log_two_div_four_mul_div_log_le_card :
    ∀ᶠ X : ℕ in atTop, log 2 / 4 * X / log X ≤ (#(primesInQuarterInterval X) : ℝ)
-- Primes/ReducedResidues.lean:138   (generic: any finset of primes above w)
theorem exists_reducedResidue_for_primes_above {w : ℕ} (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (habove : ∀ p ∈ S, w < p) :
    ∃ b ∈ reducedResidues (primorial w),
      #S ≤ (primorial w).totient * #(residueFiber S (primorial w) b)
-- WTrickDensity.lean:281   (S = primesInQuarterInterval X)
theorem exists_reducedResidue_mean_lower_bound {w N : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α)
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) * (#(primesInQuarterInterval (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean (wTrickedPrimeWeight α (primorial w) b : ZMod N → ℝ)
-- WTrickDensity.lean:534   (pure arithmetic; constant log 2 / 4 hard-wired)
theorem chebyshev_wTrick_lower_bound {W N : ℕ} (hW : 0 < W) {α : ℝ} (hα : 0 ≤ α)
    (hN : 16 ≤ N) (hscale : 16 ≤ wTrickPrimeScale W N) :
    α * log 2 / 128 ≤ (((α / (W : ℝ)) * (log 2 / 4 * (wTrickPrimeScale W N : ℝ) /
          log (wTrickPrimeScale W N)) * log (wTrickPrimeScale W N / 4 + 1 : ℕ)) / N)
-- WTrickDensity.lean:705   (eventual in N, every residue-pigeonholed class)
theorem exists_threshold_reducedResidue_mean_ge_densityTarget {k w : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N, letI : NeZero N := ⟨hN.ne'⟩
      ∃ b ∈ reducedResidues (primorial w),
        densityTarget k cutoffNormalizer ≤
          mean (wTrickedPrimeWeight (primeScale k cutoffNormalizer) (primorial w) b : ZMod N → ℝ)
```

`densityTarget k c = min (1/2) (primeScale k c * (log 2 / 4) / 100)` (`GreenTao/Parameters.lean:46`) is
a constant fixed before `w`. It is the `δ` handed to the dense Szemerédi step.

**Majorization** (`GreenTao/Majorization.lean:331`; for all `b < W` at once,
`GreenTao/CofinalPrimeTransference.lean:31`):

```lean
theorem exists_threshold_wTrickedPrimeWeight_le_cyclicMajorant (χ : SmoothSieveCutoff)
    {k W : ℕ} (hk : 3 ≤ k) (hW : 0 < W) (b : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N, letI : NeZero N := ⟨hN.ne'⟩
      ∀ n : ZMod N,
        wTrickedPrimeWeight (primeScale k χ.normalizer) W b n ≤ χ.cyclicMajorant (sieveLevel k N) W b n
```

It uses primality of `W n + b` through `normalizedSelbergMajorant_prime_of_lt`
(`Sieve/TruncatedDivisorSum.lean:222`): the Selberg square equals its normalizer at a prime above the
sieve level. **Reused unchanged**: for `A`, `1_A · weight ≤ weight ≤ ν`.

**Diagonal negligibility** (`GreenTao/DiagonalNegligibility.lean:45, 113, 202`). The height bound
`wTrickedPrimeWeight α W b n ≤ 2 α log N` (under `W + b ≤ N`). The general
`cyclicAPOffDiagMass_pos_of_count_lower_height` (any `f` with `0 ≤ f ≤ B` and `B^k < N c`). The
eventual bound `(2α log N)^k < N c`. Only the first is about the prime weight, and the A-weight
inherits it.

**Extraction** (`Primes/Extraction.lean:17`):

```lean
theorem containsAP_primes_of_wTricked_offDiagMass_pos {k N : ℕ} [NeZero N] (hk : 2 ≤ k)
    {α : ℝ} (hα : 0 < α) {W : ℕ} (hW : 0 < W) (b : ℕ)
    (hmass : 0 < cyclicAPOffDiagMass k N (wTrickedPrimeWeight α W b)) :
    ContainsAP {p : ℕ | Nat.Prime p} k
```

It goes through the general `exists_cyclicAP_of_offDiagMass_pos`
(`ArithmeticProgression/CountExtraction.lean:205`, any `f ≥ 0`), the general
`containsAP_of_cyclicAPVal_shortInterval` (`ArithmeticProgression/ShortIntervalLift.lean:18`, any
`A : Set ℕ`) and `ContainsAP.affine` (`ArithmeticProgression/Basic.lean:111`, any `A`). The
prime-specific step is `wTrickedPrimeWeight_pos_iff` (`Primes/WTrick.lean:73`): positive weight
implies `Nat.Prime (W n + b)`.

**Small lengths** (`Primes/SmallProgressions.lean:25`): `ContainsAP {p | Nat.Prime p} k` for `k ≤ 2`,
from the progression `2, 3`.

### 1.3 The inputs that do not depend on the primes

```lean
-- Szemeredi/Weighted.lean:24, 39
def HasWeightedAPCount (k N : ℕ) [NeZero N] (δ c : ℝ) : Prop :=
  ∀ g : ZMod N → ℝ, (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δ ≤ mean g → c ≤ cyclicAPCount k N g
def HasUniformWeightedAPCount (k : ℕ) (δ c : ℝ) : Prop := ∀ (N : ℕ) [NeZero N], HasWeightedAPCount k N δ c
-- Szemeredi/OrderedRemoval.lean:63
theorem exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le (k : ℕ) (hk : 2 ≤ k)
    (hordered : HasUniformOrderedPatternRemoval k (k - 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ HasUniformWeightedAPCount k δ c
-- Hypergraph/SourceFullBundleRemovalAssembly.lean:184
theorem hasUniformOrderedPatternRemoval_sourceFull (k n : ℕ) (hrank : n + 1 ≤ k) :
    HasUniformOrderedPatternRemoval k (n + 1)
-- Transference/RelativeSzemeredi.lean:40
def RelativeAPComparisonLe (r N : ℕ) [NeZero N] (ν : ZMod N → ℝ) (cutError countError : ℝ) : Prop :=
  ∀ (f g : ZMod N → ℝ), (∀ x, 0 ≤ f x) → (∀ x, f x ≤ ν x) → IsUnitBounded g →
    CutDiscrepancyLe (r + 1) f g cutError →
    |cyclicAPCount (r + 2) N f - cyclicAPCount (r + 2) N g| ≤ countError
-- Transference/RelativeSzemeredi.lean:114
theorem relativeAPCount_lower_bound_of_linearFormsCondition {r N : ℕ} [NeZero N]
    {ν f : ZMod N → ℝ} {linearFormsError cutError approximationError : ℝ}
    {p : ℝ[X]} {δ denseCount countError : ℝ}
    (happroximationError : 0 ≤ approximationError) (hcutError : 0 ≤ cutError)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x) (hν0 : ∀ x, 0 ≤ ν x)
    (hp : ApproximatesPositivePartOnUnitInterval p approximationError)
    (hLF : HasLinearFormsCondition (r + 2) N ν linearFormsError)
    (hN : Nat.Coprime N (Nat.factorial (r + 1)))
    (hconvert : (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤ cutError ^ (2 ^ (r + 1)))
    (hweighted : HasWeightedAPCount (r + 2) N δ denseCount)
    (hmean : δ + polynomialDenseModelError p cutError approximationError ≤ mean f)
    (hcomparison : RelativeAPComparisonLe r N ν (polynomialDenseModelError p cutError approximationError) countError) :
    denseCount - countError ≤ cyclicAPCount (r + 2) N f
-- Transference/RelativeCountingParameterSelection.lean:270, 310
structure RelativeCountingTransferenceParameters (r : ℕ) (densityReserve countReserve : ℝ) where ...
theorem RelativeCountingTransferenceParameters.nonempty (r : ℕ) {densityReserve countReserve : ℝ}
    (hdensity : 0 < densityReserve) (hcount : 0 < countReserve) :
    Nonempty (RelativeCountingTransferenceParameters r densityReserve countReserve)
-- GreenTao/FinalTransferenceAssembly.lean:40 (proved in Sieve/StandardCyclicLinearForms.lean:34)
def HasStandardCyclicMajorantLinearForms : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ η : ℝ, 0 < η → ∃ w : ℕ,
    exceptionalPrimeBound (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w ∧
      ∀ᶠ M : ℕ in atTop, ∀ b : ℕ, b ∈ reducedResidues (primorial w) →
        HasLinearFormsCondition k (M + 1)
          (standardSmoothSieveCutoff.cyclicMajorant (sieveLevel k (M + 1)) (primorial w) b) η
```

The 37 files under `Submission/Sieve/` that mention `Nat.Prime` do so for Euler products over primes
`p`, local factors, and the "good primes" of the affine forms. All of that concerns the majorant `ν`,
not the indicator of the primes. The linear-forms estimate is uniform over every reduced residue `b`,
which is what lets a dense set use whichever class the pigeonhole picks.

## 2. Answer to question 2

The relative counting step is **general**. `relativeAPCount_lower_bound_of_linearFormsCondition` holds
for any `f` with `0 ≤ f ≤ ν` and `δ + polynomialDenseModelError ≤ mean f`. Its comparison hypothesis
depends only on `ν`, and in the assembly it comes from `P.relativeAPComparisonLe hLFM (hν_nonneg M b)
hcoprime` (`FinalTransferenceAssembly.lean:155`), with no `f` in it. The dense input
`HasUniformWeightedAPCount` and the parameter package `RelativeCountingTransferenceParameters.nonempty`
take an arbitrary density `δ > 0`. The original proof fixes `δ = densityTarget k normalizer` only at
`FinalTransferenceAssembly.lean:62`, and uses nothing about it except `densityTarget_pos`.

So the dense form needs only the prime-specific steps redone for `A`, as the task suggested, with the
modulus-quantifier change of §3.2.

## 3. The proof for `A`

Fix `k ≥ 3`, a set `A ⊆ primes`, and `c > 0` with `c π(N) ≤ #(A ∩ [0, N])` for infinitely many `N`.
Write `α = primeScale k normalizer`.

1. **Window lemma.** There is `c₁ > 0`, depending only on `c`, with
   `c₁ Z / log Z ≤ #(A ∩ (Z/2, Z])` for infinitely many `Z`. Proof by dyadic decomposition:
   - `#(A ∩ [0,X]) ≤ π(X/2^J) + Σ_{j<J} #(A ∩ (X/2^{j+1}, X/2^j])`.
   - Chebyshev: `π(X) ≥ c_L X/log X` and `π(Y) ≤ C_U Y / log Y`.
   - Choose `J` with `2 C_U / 2^J ≤ c c_L / 2`. Then for `X ≥ 4^J` the tail costs at most half, and
     some `j < J` has `#(A ∩ window_j) ≥ (c c_L / 2J) X/log X ≥ (c c_L/2J) Z_j / log Z_j` with
     `Z_j = ⌊X/2^j⌋`.
   - `Z_j ≥ X / 2^J → ∞`.
2. **Set the density.** `c₂ = c₁/6`, `δ_A = α c₂ / 32`. Both are fixed before `w`.
3. **Transference, A-free.** Run the existing parameter selection with `δ := δ_A`. This gives
   `w`, `c_count > 0` and `M_thr` such that for **every** `M ≥ M_thr` with `M + 1` prime, every reduced
   `b` mod `W = primorial w`, and every `f` with `0 ≤ f ≤ wTrickedPrimeWeight α W b` and
   `δ_A ≤ mean f`, we have `c_count ≤ cyclicAPCount k (M+1) f`.
4. **Modulus selection.** Take a good `Z` from step 1 that is large in terms of `W`, `M_thr`, the height
   threshold and `w`. Let `m = ⌈Z/W⌉`. Bertrand gives a prime `q ∈ (8m, 16m]`, so
   `⌊q/8⌋ ∈ [m, 2m]` and `X = W ⌊q/8⌋ ∈ [Z, 2Z + 2W] ⊆ [Z, 3Z]`. Then `(X/4, X] ⊇ ((Z+W)/2, Z]`, so
   `#(A ∩ (X/4, X]) ≥ c₁ Z/log Z − (W/2 + 1) ≥ (c₁/2) Z / log Z ≥ c₂ X / log X`.
5. **Residue pigeonhole for `A`.** Every element of `A ∩ (X/4, X]` exceeds `w`, so it is coprime to
   `W`. The existing `exists_reducedResidue_for_primes_above`, applied to
   `S = (primesInQuarterInterval X).filter (· ∈ A)`, gives a reduced `b` with
   `#S ≤ φ(W) #(S_b)`. The injection `p ↦ (p − b)/W` into `greenTaoInterval q`, as in
   `WTrickDensity.lean:145–341`, then gives
   `mean (wTrickedSetWeight A α W b) ≥ (α/W) #S log(X/4+1) / q ≥ α c₂ / 32 = δ_A`.
   The arithmetic is that of `chebyshev_wTrick_lower_bound` with `log 2 / 4` replaced by `c₂`.
6. **Count, mass, extraction.** Step 3 with `f = wTrickedSetWeight A α W b` gives
   `c_count ≤ cyclicAPCount k q f`. The height bound `f ≤ 2α log q` and
   `cyclicAPOffDiagMass_pos_of_count_lower_height` give positive off-diagonal mass. Extraction with
   `(wTrickedSetWeight_pos_iff).2 : W n + b ∈ A` gives `ContainsAP A k`.
7. **Lengths `k ≤ 2`** come from `ContainsAP A 3` via `ContainsAP.take`. No separate argument is needed.

### 3.1 Every place where the original uses a property that a dense `A` lacks

| # | original use | property of all primes | what `A` has | fix |
|---|---|---|---|---|
| P1 | `Chebyshev.lean:214` inside `exists_threshold_reducedResidue_mean_ge_densityTarget` (`WTrickDensity.lean:705`) | `≥ (log 2/4) X/log X` primes in `(X/4, X]` for **every** large `X` | `≥ c π(N)` elements in `[0, N]` for **infinitely many** `N`, with no window control | window lemma (§3 step 1) |
| P2 | `ReducedResidueCofinalTransference.lean:191–204`, `AsymptoticAssembly.lean:43` | density holds eventually in the modulus, so the modulus can be chosen afterwards by `Nat.exists_infinite_primes` | density only at scales tied to `A` | transference for all large prime moduli (§4.2), then Bertrand (§3 step 4) |
| P3 | `densityTarget` (`Parameters.lean:46`) | one absolute density, independent of the set | density `δ_A ∝ c₁` | parameterize the assembly by `δ > 0` |
| P4 | `wTrickedPrimeWeight_pos_iff` in extraction | positive weight ⇒ prime | — | `wTrickedSetWeight_pos_iff`: positive ⇒ in `A` (and prime) |
| P5 | `SmallProgressions.lean:14` (`2, 3`) | `2, 3` are prime | `A` may miss both | take the `k = 3` progression and truncate it |
| P6 | the residue class: the original takes the class given by pigeonholing **all** primes | the pigeonhole is over all primes in the window | only `A`'s primes | pigeonhole over `A`'s primes, using `exists_reducedResidue_for_primes_above`, which is generic in `S` |

The proof needs no lower bound for primes of `A` in **every** residue class. It needs one class
`b` that carries a `1/φ(W)` share of `A`'s mass. The sieve side is uniform over all reduced classes
(`HasStandardCyclicMajorantLinearForms`, `eventually_all_residues_wTrickedPrimeWeight_le_cyclicMajorant`),
so any class is acceptable. The prime number theorem in progressions is not used, either here or in
the original.

The constants need one check, P7. The original's density target `densityTarget ≤ α (log 2/4)/100`
lies below the Chebyshev mean `α log 2/128`. For `A` the mean is `α c₂/32`, and we pass exactly
`δ_A = α c₂/32`, or `α c₂/64` to leave room. The transference accepts any `δ > 0`, because the dense
count `denseCount` and the parameter package are chosen *after* `δ`.

## 4. New Lean statements

All of these sit in namespace `Submission.GreenTao` (so the vendored names resolve unqualified) or in
`GreenTaoDense`, in new files that import the vendored modules.

### 4.1 The A-weight

```lean
open Classical in
/-- `1_A(W n + b)` times the W-tricked prime weight. -/
noncomputable def wTrickedSetWeight {N : ℕ} [NeZero N] (A : Set ℕ) (α : ℝ) (W b : ℕ) (n : ZMod N) : ℝ :=
  if wTrickedValue W b n ∈ A then wTrickedPrimeWeight α W b n else 0

theorem wTrickedSetWeight_nonneg (hα : 0 ≤ α) : 0 ≤ wTrickedSetWeight A α W b n
theorem wTrickedSetWeight_le : wTrickedSetWeight A α W b n ≤ wTrickedPrimeWeight α W b n   -- needs 0 ≤ α
theorem wTrickedSetWeight_pos_iff (hα : 0 < α) (hW : 0 < W) :
    0 < wTrickedSetWeight A α W b n ↔
      n.val ∈ greenTaoInterval N ∧ Nat.Prime (wTrickedValue W b n) ∧ wTrickedValue W b n ∈ A
```

### 4.2 Transference for every large prime modulus, for every sub-weight (A-free)

```lean
/-- The transference output of `FinalTransferenceAssembly`, for every density `δ > 0`,
every large prime modulus, and every weight below the W-tricked prime weight. -/
def HasPrimeModulusSubweightCounts : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ δ : ℝ, 0 < δ →
    ∃ (w : ℕ) (c : ℝ), 0 < c ∧
      ∀ᶠ M : ℕ in atTop, Nat.Prime (M + 1) →
        ∀ b ∈ reducedResidues (primorial w), ∀ f : ZMod (M + 1) → ℝ,
          (∀ x, 0 ≤ f x) →
          (∀ x, f x ≤ wTrickedPrimeWeight (primeScale k standardSmoothSieveCutoff.normalizer) (primorial w) b x) →
          δ ≤ mean f → c ≤ cyclicAPCount k (M + 1) f

-- adapted from ReducedResidueCofinalTransference.lean:55 (same hypotheses; conclusion "eventually,
-- for every prime M+1, for every f ≤ weight" instead of "∃ prime M+1, for the weight itself")
theorem eventually_prime_subweight_count_of_eventually ... :
    ∀ᶠ M : ℕ in atTop, Nat.Prime (M + 1) → ∀ b ∈ reducedResidues W, ∀ f : ZMod (M + 1) → ℝ,
      (∀ x, 0 ≤ f x) → (∀ x, f x ≤ wTrickedPrimeWeight α W b x) →
      δ + polynomialDenseModelError p cutError approximationError ≤ mean f →
      denseCount - countError ≤ cyclicAPCount (r + 2) (M + 1) f

-- adapted from FinalTransferenceAssembly.lean:56 (density := δ instead of densityTarget)
theorem hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms
    (hremoval : HasOrderedRemovalForAllAPLengths) (hsieve : HasStandardCyclicMajorantLinearForms) :
    HasPrimeModulusSubweightCounts

theorem hasPrimeModulusSubweightCounts : HasPrimeModulusSubweightCounts :=
  hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms
    (fun k hk => by  -- as in Submission.lean:13-19
      have hrank : k - 1 = (k - 2) + 1 := by omega
      rw [hrank]; exact hasUniformOrderedPatternRemoval_sourceFull k (k - 2) (by omega))
    hasStandardCyclicMajorantLinearForms
```

In the proof of the second theorem, the coprimality with `(r+1)!` comes from primality of `M + 1` and
`r + 1 < M + 1`, as at `ReducedResidueCofinalTransference.lean:137–144`.
`relativeAPCount_lower_bound_of_linearFormsCondition` is then applied with `hfν` given by
`(hf b x).trans (hmajorM b hb x)`.

### 4.3 Density selection for `A`

```lean
/-- The `A`-primes of the quarter interval. -/
def quarterIntervalSet (A : Set ℕ) (X : ℕ) : Finset ℕ := (primesInQuarterInterval X).filter (· ∈ A)

-- adapted from WTrickDensity.lean:145–341 (classA := (quarterIntervalResidueClass W N b).filter (· ∈ A))
theorem exists_reducedResidue_setWeight_mean_lower_bound {A : Set ℕ} {w N : ℕ} [NeZero N] {α : ℝ}
    (hα : 0 ≤ α) (hw : w ≤ wTrickPrimeScale (primorial w) N / 4) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) * (#(quarterIntervalSet A (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean (wTrickedSetWeight A α (primorial w) b : ZMod N → ℝ)

-- adapted from WTrickDensity.lean:534 (log 2 / 4 ↦ any c₂ ≥ 0)
theorem wTrick_lower_bound_of_count {W N : ℕ} (hW : 0 < W) {α c₂ : ℝ} (hα : 0 ≤ α) (hc₂ : 0 ≤ c₂)
    (hN : 16 ≤ N) (hscale : 16 ≤ wTrickPrimeScale W N) :
    α * c₂ / 32 ≤ (((α / (W : ℝ)) * (c₂ * (wTrickPrimeScale W N : ℝ) / log (wTrickPrimeScale W N)) *
        log (wTrickPrimeScale W N / 4 + 1 : ℕ)) / N)
```

### 4.4 Elementary lemmas (new)

```lean
-- Chebyshev upper bound (from Mathlib's Chebyshev.theta_le_log4_mul_x)
theorem primeCounting_le_mul_div_log {Y : ℕ} (hY : 2 ≤ Y) : (π Y : ℝ) ≤ 4 * Y / Real.log Y
-- Chebyshev lower bound (from Chebyshev.psi_le_primeCounting_mul_log and Chebyshev.psi_ge,
-- or from the vendored eventually_log_two_div_four_mul_div_log_le_card)
theorem eventually_mul_div_log_le_primeCounting : ∀ᶠ X : ℕ in atTop, Real.log 2 / 4 * X / Real.log X ≤ π X
-- dyadic decomposition
theorem card_filter_range_le_sum_windows (A : Set ℕ) (X J : ℕ) :
    #((range (X+1)).filter (· ∈ A)) ≤ #((range (X / 2^J + 1)).filter (· ∈ A)) +
      ∑ j ∈ range J, #((Ioc (X / 2^(j+1)) (X / 2^j)).filter (· ∈ A))
-- the window lemma
theorem PrimesRelUpperDensityPos.frequently_window {A : Set ℕ} (hA : A ⊆ {p | p.Prime})
    (h : ZInQ.PrimesRelUpperDensityPos A) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ᶠ Z : ℕ in atTop, c₁ * Z / Real.log Z ≤ #((Ioc (Z / 2) Z).filter (· ∈ A))
-- modulus selection
theorem exists_prime_modulus_of_window {A : Set ℕ} {W Z : ℕ} (hW : 0 < W) (hZ : 2 * W ≤ Z) ... :
    ∃ q : ℕ, q.Prime ∧ 8 * (Z / W) < q ∧ Z ≤ wTrickPrimeScale W q ∧ wTrickPrimeScale W q ≤ 3 * Z ∧
      #((Ioc (Z/2) Z).filter (· ∈ A)) ≤ #(quarterIntervalSet A (wTrickPrimeScale W q)) + (W / 2 + 1)
```

Mathlib at `56a00585` has `Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_le_primeCounting_mul_log`,
`Chebyshev.psi_ge` (`Mathlib/NumberTheory/Chebyshev.lean`) and Bertrand's postulate
`Nat.exists_prime_lt_and_le_two_mul`. Mathlib has no explicit `π(Y) ≪ Y/log Y`. The proof goes through
`π(Y) ≤ √Y + θ(Y)/log √Y ≤ (1 + 2 log 4) Y / log Y`.

### 4.5 Extraction and final assembly

```lean
-- adapted from Primes/Extraction.lean:17
theorem containsAP_of_wTrickedSetWeight_offDiagMass_pos {A : Set ℕ} {k N : ℕ} [NeZero N] (hk : 2 ≤ k)
    {α : ℝ} (hα : 0 < α) {W : ℕ} (hW : 0 < W) (b : ℕ)
    (hmass : 0 < cyclicAPOffDiagMass k N (wTrickedSetWeight A α W b)) : ContainsAP A k

theorem containsAP_of_primesRelUpperDensityPos (hT : HasPrimeModulusSubweightCounts)
    {A : Set ℕ} (hA : A ⊆ {p | p.Prime}) (hd : ZInQ.PrimesRelUpperDensityPos A) (k : ℕ) : ContainsAP A k

-- in ZInQKernel (bridge), the target:
theorem ZInQ.greenTaoDense : ZInQ.GreenTaoDense
```

`ZInQ.ContainsArbitraryAPs` and `LeanEval.NumberTheory.ContainsArbitraryAPs` have the same body, so the
bridge is `containsArbitraryAPs_iff` plus `Iff.rfl`/`id`.

## 5. Files

No vendored file is modified. New files, under `ThirdParty/GreenTao/GreenTaoDense/` (modules
`GreenTaoDense.*`; add `"GreenTaoDense"` to the `roots` of lean_lib `GreenTaoVendor`, or give it its own
lean_lib with the same `srcDir` and `autoImplicit = false`). Files marked "adapted" are derivative works
of the Apache-2.0 sources. Each carries a header naming the source file at commit `0dc67d8`, the
license, and the statement "Modified 2026 for the diophantine-z-q project: generalized from the set of
primes to a subset `A`" (Apache-2.0 §4(b)). `ThirdParty/GreenTao/NOTICE.md` (from gt-import) gets one
line listing them.

| new file | source | content | est. lines |
|---|---|---|---|
| `GreenTaoDense/SetWeight.lean` | adapted from `Primes/WTrick.lean` | §4.1 | 60 |
| `GreenTaoDense/PrimeModulusTransference.lean` | adapted from `GreenTao/ReducedResidueCofinalTransference.lean:55–157` and `GreenTao/FinalTransferenceAssembly.lean:56–184` | §4.2 | 200 |
| `GreenTaoDense/SetDensity.lean` | adapted from `Primes/WTrickDensity.lean:145–341, 534–590` | §4.3 | 220 |
| `GreenTaoDense/Chebyshev.lean` | new | Chebyshev upper and lower bounds for `π` | 80 |
| `GreenTaoDense/Window.lean` | new | dyadic decomposition, window lemma, Bertrand modulus selection | 220 |
| `GreenTaoDense/Extraction.lean` | adapted from `Primes/Extraction.lean`, `GreenTao/CofinalPrimeModulusAssembly.lean:77–106` | §4.5 extraction and mass | 90 |
| `GreenTaoDense/Assembly.lean` | new | `containsAP_of_primesRelUpperDensityPos` | 100 |
| `ZInQKernel/External/GreenTaoDense.lean` | new (project license) | `ZInQ.greenTaoDense`, and a `Main` variant without the hypothesis | 30 |

`Chebyshev.lean` and `Window.lean` import only Mathlib and the definition of
`PrimesRelUpperDensityPos`. They can be written and checked now, before gt-import lands. To keep the
vendored library free of `ZInQKernel` imports, restate the density condition there as a local
`def` with the same body. The bridge file closes the gap with `Iff.rfl`.

## 6. Order of work and effort

| step | work | depends on | tier |
|---|---|---|---|
| S1 | `Chebyshev.lean`, `Window.lean` (scratch first, then move) | Mathlib only | **medium**: about 300 lines of real analysis with floors and logs; the only new mathematics |
| S2 | `SetWeight.lean` | gt-import builds | **small**: copy with an `if` |
| S3 | `PrimeModulusTransference.lean` | gt-import, S2 not needed | **small–medium**: copy two proofs, change one quantifier; risk: the `simpa only [hcolors, W, ν]` steps around `r + 2 = k` |
| S4 | `SetDensity.lean` | S2 | **small–medium**: copy about 200 lines with `filter (· ∈ A)` threaded through; `residueFiber` of a filter is a filter of `residueFiber` (`Finset.filter_filter`, `filter_comm`) |
| S5 | `Extraction.lean` | S2 | **small** |
| S6 | `Assembly.lean` (steps 2–7 of §3) | S1, S3, S4, S5 | **medium**: quantifier bookkeeping; choosing `Z` past five thresholds |
| S7 | bridge and `Main` variant in `ZInQKernel` | S6; gt-import wired into the build | **small**, but importing the vendored library (117k lines) into `ZInQKernel` costs build time; keep the bridge in a module that `Main` imports only for this variant |

Total: about 2–4 agent-days. The risky parts are S1 (analysis) and S6 (bookkeeping). The deep layers
are untouched.

## 7. First step and its success criterion

**S1, in scratch.** `scratch/gt-dense-plan/Window.lean`, importing only Mathlib and restating
`PrimesRelUpperDensityPos` verbatim:

```lean
theorem frequently_window {A : Set ℕ} (hA : A ⊆ {p | p.Prime}) (h : PrimesRelUpperDensityPos A) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ᶠ Z : ℕ in atTop, c₁ * Z / Real.log Z ≤ #((Finset.Ioc (Z / 2) Z).filter (· ∈ A))
```

Success criterion: `lake env lean scratch/gt-dense-plan/Window.lean` succeeds against the repository's
Mathlib with no `sorry`, and `#print axioms frequently_window` shows only `propext`,
`Classical.choice`, `Quot.sound`. The pigeonhole over residues for `A` (a two-line corollary of the
vendored `exists_reducedResidue_for_primes_above`) is tested in the same file through a
Mathlib-only restatement. See §8 for the status of this optional step.

## 8. Status of the optional Lean check

See the end of this file (updated after the scratch run) and `scratch/gt-dense-plan/log.md`.
