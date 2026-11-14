# tyz-318 results log

Target: `Lemma318Literal HHprime` (verbatim copy of `Package.Lemma318Literal`, from scratch/cm-bridge/Bridge.lean §0),
TYZ Lemma `torsion2` (Lemma 3.18): torsion of `A(ℍ'_n)` is killed by `2(1+[i])`.

## Route (no ramification at odd primes, no Lubin–Tate)
1. Odd torsion: reduction at a prime `p ≡ 3 (mod 8)`, `p ≡ 1 (mod q)` for all odd `q ∣ nℓ` (Dirichlet, in Mathlib);
   such `p` is inert in every `K_{d₀}` (`d₀ ∣ n`, `d₀ ≡ 5 (8)`), so (GLUE) every prime of `ℍ'_n` over `p` has
   residue field inside `F_{p²}`; `A` is supersingular at `p` and (LEAF) `Ã(F_{p²})` is killed by `p+1`;
   Tau Ceti `eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero` (Silverman VII.3.1(b), proved, vendored) gives
   `A(ℍ'_n)[ℓ] ↪ Ã(k)`, and `ℓ ∤ p+1`.
2. 2-primary torsion: a 2-power torsion point outside `A[(1+i)³]` has a multiple `S ∈ A(K)` with `4S = 0`,
   `2(1+i)S ≠ 0`; then `x(S)` satisfies `x² − 2ex + 4 = 0`, `e = x(2S)`, `e² = −4`, so `(i(x−e)/2)² = 2` and
   `√2 ∈ K`. (GLUE, TYZ's Step 3) `√2 ∉ ℍ'_n`.

## Findings
- [VERIFIED, computed, scratch/tyz-318/ss_check.py, pure Python] leaf sanity: for p ∈ {3,7,11,19,23,31,43,47},
  `y² = x³ + 4x` has `(p+1)²` points over `F_{p²}`, `p+1` over `F_p`, and every `F_{p²}`-point is killed by `p+1`.

## Compile outcomes
- 2026-11-13 23:2x: `lake build` of RingClassBridge, RingClassTwo, Tau Ceti TorsionReduction (deps) OK.
- [VERIFIED, compiled] `lake env lean scratch/tyz-318/Lemma318.lean`: no errors;
  `#print axioms lemma318Literal_HHprime_of` = [propext, Classical.choice, Quot.sound]. No `sorry`.
  Main theorem: `SupersingularExponentA → HHprimeFrobSq → SqrtTwoNotInHHprime → Lemma318Literal HHprime`
  (and `package_lemma318Literal_HHprime_of` for `Package.Lemma318Literal`); copy checked by `rfl`.

## Statements (scratch/tyz-318/Lemma318.lean §1)
- LEAF `SupersingularExponentA`: ∀ p prime, p%4=3, ∀ field k, CharP k p, (∀ r, r^(p²)=r) →
  ∀ P : (shortCurve (4:k)).toAffine.Point, (p+1)•P = 0. STANDARD (supersingular y²=x³+x, Silverman AEC V.4.5
  UNVERIFIED number; φ² = [−p]).
- GLUE `HHprimeFrobSq`: n%8=5 sqfree, p odd prime ∤ n, (−d₀/p) = −1 ∀ d₀∣n, d₀%8=5 →
  ∀ prime 𝔓 ∋ p of 𝓞(HHprime n), ∀ a, a^(p²) − a ∈ 𝔓. (ring class field theory; sketch in report §3.1)
- GLUE `SqrtTwoNotInHHprime`: n%8=5 sqfree → ∀ s ∈ HHprime n, s² ≠ 2. (TYZ Step 3; report §3.2 sketch, SPECULATIVE)
- [VERIFIED, compiled, 2026-11-13 ~23:55] §8 `hhprimeFrobSq_of : HprimeFrobOrderTwo → HHprimeFrobSq` (compositum step:
  Mathlib Frobenius `IsArithFrobAt.exists_of_isInvariant`, lift to `Gal(ℚ̄/ℚ)`, `h²` fixes `L_n(i)` generators
  (`s² ∈ ℚ`) and each `H'_{d₀}`); finer main theorem `lemma318Literal_HHprime_of'`
  (SupersingularExponentA, HprimeFrobOrderTwo, SqrtTwoNotInHHprime); axioms standard.
- GLUE `HprimeFrobOrderTwo`: d%8=5 sqfree, p odd prime ∤ d, (−d/p) = −1, h ∈ Gal(ℚ̄/ℚ) Frobenius on `H'_d` at a
  prime Q ∋ p of 𝓞(Hprimebar d) → h² = 1 on `H'_d`.
- [AI review, subagent, read-only, no Lean] the three §1 Props: all OK (true, non-vacuous, faithful); √2 sketch
  sound; flagged: say explicitly that Artin functoriality is transported through `embed d₀` (fine since
  `H_{d₀,4}`, `H'_{d₀}` are Galois over ℚ); `[DecidableEq k]` binder in the leaf is harmless. Not checked:
  TYZ's Step 3 wording (needs the source; HUMAN CHECK).
- [VERIFIED, compiled, 2026-11-14 ~01:15] §9 (merged from a temporary StepC.lean): `prime_eq_span_of_inert`,
  `hprime_inert_split` (Step C: residue field ⊆ F_{p²}, trivial inertia in Gal(H'_d/K_d), from ring-class's
  `mem_splitSet_iff` + Mathlib `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank`), transport `psi0`, `tauQ`,
  `tau2`, `hprimeFrobOrderTwo_aux`; **`hprimeFrobOrderTwo : HprimeFrobOrderTwo`** and
  **`hhprimeFrobSq : HHprimeFrobSq`** proved (no hypotheses).
  Final: `lemma318Literal_HHprime_of_ss_sqrtTwo : SupersingularExponentA → SqrtTwoNotInHHprime → Lemma318Literal HHprime`
  (+ `package_…` for `Package.Lemma318Literal`); `#print axioms` = [propext, Classical.choice, Quot.sound].
  Whole file compiles in ~20 s (lake env lean), no sorry.
- [VERIFIED, compiled, 2026-11-13 ~23:55 host clock] `sqrtTwo_not_mem_HHprime_of_single`: √2 ∉ ℍ'_n when n is the
  only divisor d₀ ≡ 5 (8) of n (ℍ'_n = H'_n; ring-class `not_adjSqrt_two_le_Hprime` transported through `embed n`);
  `lemma318_at` (per-n form) and `lemma318_at_single`: TYZ Lemma torsion2 at such n from the leaf
  `SupersingularExponentA` alone. Axioms standard.
- [VERIFIED, computed, scratch/tyz-318/trace_check.py, exact rational arithmetic] Route A element for √2 ∉ ℍ'_n:
  β = i∏_{q|n}(1+√q*)/2, α = 1+2β ∈ 𝓞_{L_n(i)}: Tr_{F/K_{d₀}}(β) = √−d₀, N_{F/K_{d₀}}(α) ≡ 1+2√−d₀ (mod 4),
  N(α)(3−2√−d₀) ∈ ℤ+4𝓞_K, for n ∈ {5,13,21,85,165,205,357,1365} and all d₀ ∣ n, d₀ ≡ 5 (8) (15 pairs). ALL OK.
  (The script's list also contained 1105, which is ≡ 1 (mod 8) and was filtered out.)
- Route A (report §3.2) not formalized: needs multiquadratic Galois/norm computations in L_n(i), Chebotarev over
  L_n(i) for Pic(ℤ+4𝓞_F) (Tau Ceti has the tools), Frobenius transport. SPECULATIVE estimate 1–2 tasks.
