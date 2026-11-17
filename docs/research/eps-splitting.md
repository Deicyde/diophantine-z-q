# eps-splitting: `ε_D(p)` is the splitting character of `ℚ(√D)`, proved in Lean; the GZ leaf's twist is now the print's

Status: research note (task eps-splitting, 2026-11-17). Branch `wip/eps-splitting`, base `wip/hgz-steps` 92fd272e
with `origin/main` (e1b31749) merged.

New Lean files (nothing else under `ZInQKernel/` edited):
- `ZInQKernel/Contrib/OneProof/GrossZagierSplit/QuadSplit.lean`: the number theory (imports Mathlib and
  hgz-steps' `GrossZagierScheme/EpsD.lean` only).
- `ZInQKernel/Contrib/OneProof/GrossZagierSplit.lean`: the new leaf `GZSplit.GrossZagierCurveCdSplit` and the
  bridge to `hGZ`.

Scratch, checks and log: `scratch/eps-splitting/`.

Marks. **VERIFIED**: compiled, computed, or read in a source named here. **STANDARD**: published, exact reference.
**SPECULATIVE**: an assessment. This host has no copy of Gross–Zagier. Literature locators are UNVERIFIED unless
they come from the queue9 reading quoted by hgz-steps.

---

## 0. Main result

**Theorem (Lean, no `sorry`, standard axioms).** Let `D < 0` be a fundamental discriminant (Mathlib's
`Int.IsFundamentalDiscr D`), `K` a number field with `[K : ℚ] = 2`, and `δ ∈ K` with `δ² = D`, so `K = ℚ(√D)`.
Then for every prime `p`:

```lean
theorem ZInQ.EpsSplit.splitType_epsD (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : Module.finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) {p : ℕ} (hpp : p.Prime) :
    SplitType K p (ZInQ.HGZSteps.epsD D p)
-- SplitType K p v := (IsSplitIn K p ↔ v = 1) ∧ (IsInertIn K p ↔ v = -1) ∧ (IsRamifiedIn K p ↔ v = 0)
```

Here `ε_D = ZInQ.HGZSteps.epsD D` is hgz-steps' Kronecker symbol `(D/·)`, the twist used by the leaf
`GZSch.GrossZagierCurveCd`. The three conditions are defined through prime ideals of `𝓞 K` (Mathlib):

| predicate | definition |
| --- | --- |
| `IsSplitIn K p` | two distinct prime ideals `P ≠ Q` of `𝓞 K` lie over `pℤ` (`Ideal.primesOver`) |
| `IsInertIn K p` | `p 𝓞_K` is a prime ideal |
| `IsRamifiedIn K p` | some prime of `𝓞 K` over `p` has `Ideal.ramificationIdx > 1` |

Two consequences:
- `quadChar_eq_epsD`: the quadratic character of `K`, `quadChar K`, equals `ε_D` at every `n : ℕ`. It is completely
  multiplicative, with value `1`, `−1`, `0` at a prime that splits, is inert, or ramifies, and `0` at `0`.
- `epsD_eq_one_iff_isSplitIn`, `epsD_eq_neg_one_iff_isInertIn`, `epsD_eq_zero_iff_isRamifiedIn`: the three
  statements separately.

**Use: the leaf's twist is now literally the print's.** The new leaf `ZInQ.GZSplit.GrossZagierCurveCdSplit` is
hgz-steps' `GZSch.GrossZagierCurveCd` with two changes:
- the Heegner hypothesis reads "every prime `p ∣ N` splits in `K`" (`IsSplitIn K p`);
- the twist is by the quadratic character of `K` (`quadChar K`).

Both are as in Gross–Zagier. The field `K` (with `δ`) is introduced before the Heegner hypothesis. The leaf feeds
`frozenTarget`:

```lean
theorem ZInQ.GZSplit.grossZagierAlgOptCd_of_split :
    ZInQ.GZSplit.GrossZagierCurveCdSplit → ZInQ.GZAlg.GrossZagierAlgOptCd   -- the binder hGZ
theorem ZInQ.GZSplit.grossZagierCurveCd_of_split :
    GrossZagierCurveCdSplit → ZInQ.GZSch.GrossZagierCurveCd
theorem ZInQ.GZSplit.grossZagierCurveCdSplit_of_curveCd :
    ZInQ.GZSch.GrossZagierCurveCd → GrossZagierCurveCdSplit          -- the leaves are equivalent
```

**Verdict.** The reviewer's possible step on `ε_D` is removed in either reading of GZ's `ε`:
- read as the Kronecker symbol: hgz-steps' leaf applies;
- read as the character of `K` defined by splitting: the new leaf applies.

The two leaves are equivalent in Lean. The new leaf is rated **LEAF, printed form (direct instance)** (§3). Its
count relative to hgz-steps: LEAF → LEAF, **no change**. One definitional reading is gone: hgz-steps' "Not
formalized, textbook" item ("`(D/p)` is the splitting character of `p` in `O_K`").

## 1. The proof (all in `GrossZagierSplit/QuadSplit.lean`)

1. **`𝓞_K = ℤ[θ]`, `θ = (D + δ)/2`** (`exists_int_repr`, `adjoin_thetaO_eq_top`).
   - `{1, θ}` is a `ℚ`-basis of `K` (`exists_repr`: `θ ∉ ℚ` because `D < 0` is not a rational square).
   - For an integral `x = s + tθ ∉ ℚ`: `minpoly ℚ x = X² − (2s + tD) X + (s² + sDt + t²(D² − D)/4)`, by degree.
     It has integer coefficients (`minpoly.isIntegrallyClosed_eq_field_fractions'`).
   - Its discriminant `t²D` is an integer. With `D` (or `D/4`) squarefree this forces `t ∈ ℤ`; in the case
     `D = 4m`, `m ≡ 2, 3 (mod 4)` rules out `t ∈ ½ + ℤ`.
   - Then `2s ∈ ℤ` and a parity argument on the norm gives `s ∈ ℤ` (`rat_int_of_sq_mul`, `int_of_coeffs`).
   - The case `x ∈ ℚ` is `minpoly = X − s`.
2. **`minpoly ℤ θ = X² − D X + (D² − D)/4`** (`minpoly_thetaO`): `θ` is a root, and degree `≥ 2` since `θ ∉ ℤ`.
3. **Kummer–Dedekind** (Mathlib: `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`,
   `RingOfIntegers.ZModXQuotSpanEquivQuotSpan`, `ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'`).
   `exponent θ = 1` by step 1 (`RingOfIntegers.exponent_eq_one_iff`), so it applies at every `p`, including
   `p = 2` and `p ∣ D`. With `ḡ = minpoly ℤ θ mod p`:
   - `isInertIn_iff`: `p` is inert iff `ḡ` is irreducible (`𝓞/p ≅ 𝔽_p[X]/(ḡ)` is a domain);
   - `isSplitIn_iff`: `p` splits iff `ḡ` has two distinct monic irreducible factors;
   - `isRamifiedIn_iff`: `p` ramifies iff some factor has multiplicity `> 1`.
4. **The three factorization types** of a monic quadratic over `𝔽_p`:
   - `splitType_of_irreducible`: irreducible gives `SplitType K p (−1)`;
   - `splitType_of_eq_mul`: `(X − a)(X − b)` with `a ≠ b` gives `SplitType K p 1`;
   - `splitType_of_eq_mul_self`: `(X − a)²` gives `SplitType K p 0`.

   Multiplicities come from counts in `normalizedFactors`.
5. **`ε_D(p)` picks the type** (`splitType_epsD`). `ḡ = X² − D̄ X + c̄` with `4c̄ = D̄² − D̄`.

   | case | `ε_D(p)` | `ḡ` | type |
   | --- | --- | --- | --- |
   | `p` odd, `p ∣ D` | `0` (Legendre) | `X²` | ramified |
   | `p` odd, `D` a nonzero square `s²` mod `p` | `1` | `(X − (D+s)/2)(X − (D−s)/2)` | split |
   | `p` odd, `D` not a square mod `p` | `−1` | irreducible (a root `r` would give `D = (2r − D)²`) | inert |
   | `p = 2`, `D ≡ 1 (mod 8)` | `χ₈(D) = 1` | `X(X + 1)` | split |
   | `p = 2`, `D ≡ 5 (mod 8)` | `χ₈(D) = −1` | `X² + X + 1` | inert |
   | `p = 2`, `D = 4m`, `m ≡ 2 (mod 4)` | `χ₈(D) = 0` | `X²` | ramified |
   | `p = 2`, `D = 4m`, `m ≡ 3 (mod 4)` | `χ₈(D) = 0` | `(X + 1)²` | ramified |
6. **`quadChar_eq_epsD`.** Both sides are completely multiplicative products over the factorization of `n`. At
   primes they agree by step 5 and `epsD_prime_trichotomy`. At `0` both are `0` (`|D| ≠ 1`).

The leaf only needs odd `D` (`IsOddImagFundDisc`), but the theorem covers every negative fundamental discriminant.

## 2. The leaf and the bridge (`GrossZagierSplit.lean`)

`GrossZagierCurveAtSplit E` differs from `GZSch.GrossZagierCurveAt E` only in these binders. Everything else
(`N`, `f`, `X`, `ι`, `π`, cusp, `β`, `R`, `τ`, `x`, `ιK`, `n`, `y`, `F`) is verbatim.

| hgz-steps (`GrossZagierCurveAt`) | eps-splitting (`GrossZagierCurveAtSplit`) |
| --- | --- |
| `(∀ p, p.Prime → p ∣ N → epsD D p = 1)` | `∀ K … δ, δ² = D →` then `(∀ p, p.Prime → p ∣ N → IsSplitIn K p)` |
| `K, δ` introduced after the Heegner points | `K, δ` introduced before the Heegner hypothesis |
| `IsEntireCont (coeff f · * epsD D ·) 2 G` | `IsEntireCont (coeff f · * quadChar K ·) 2 G` |

`GrossZagierCurveCdSplit` restricts `E` to the short models in the isogeny class of `C_d` (`d ≡ 5 (mod 8)`
squarefree), as `GrossZagierCurveCd` does.

`grossZagierCurveAt_of_split` and `grossZagierCurveAtSplit_of_curveAt` translate the two binders with
`epsD_eq_one_iff_isSplitIn` and `twist_quadChar_eq` (from `quadChar_eq_epsD`). `IsOddImagFundDisc D` gives
`Int.IsFundamentalDiscr D` through Mathlib's `isFundamentalDiscr_iff_squarefree`.

## 3. Rating of `GZSplit.GrossZagierCurveCdSplit`

**LEAF, printed form (direct instance).** Reasons:
- **The statement is the print's.** GZ's Heegner hypothesis is that every prime dividing `N` splits in `K`. Their
  twist is by the quadratic character `ε` of `K/ℚ`, with `L(E/K, s) = L(f, s) L(f ⊗ ε, s)` (IV (0.4), p. 268 per the
  queue9 reading, UNVERIFIED here). Both now appear in that form, over Mathlib's ideals of `𝓞 K`. The rest is
  hgz-steps' leaf, rated printed form there (morphism `π : X₀(N) → E` of `ℚ`-schemes, `π(∞) = O`, `ℂ`-points
  `τ_r`).
- **It is not stronger than the print, and not vacuous.** It is equivalent in Lean to hgz-steps' leaf (both
  directions proved). That leaf was rated weaker than or equal to the print, and non-vacuous: hgz-steps' bridge
  builds every hypothesis.
- **The definitions are genuine.** `IsSplitIn`, `IsInertIn` and `IsRamifiedIn` use Mathlib's `primesOver`,
  `Ideal.IsPrime` and `Ideal.ramificationIdx` on `𝓞 K`.
  - `quadChar K` is the multiplicative function with these values at primes. By `quadChar_eq_epsD` it is the
    Dirichlet character of `K` of conductor `|D|` (VERIFIED as the equality with `(D/·)`).
  - `IsSplitIn` (two distinct primes over `p`) is the standard meaning in a quadratic field. With `Σ e f = 2`
    this is `p 𝓞 = 𝔭𝔭'`, `𝔭 ≠ 𝔭'`, and the trichotomy is proved.
- **Remaining readings: none new.** hgz-steps' two definitional readings (the canonical model `X₀(N)_ℚ`, the
  point `τ`) are unchanged. Its third item (`ε_D` as the splitting character) is now a theorem.

Counting: LEAF → LEAF relative to hgz-steps, no GLUE change. Relative to `main` (binder type
`GZAlg.GrossZagierAlgOptCd`, rated GLUE pending reading), the fold is hgz-steps' **GLUE −1**.

## 4. Fold (manual: `hGZ` is a binder of `frozenTarget`, not a bundle field)

Files in `scratch/eps-splitting/`:
- `fold-spec.md`: import `GrossZagierSplit`, retype `hGZ` to `ZInQ.GZSplit.GrossZagierCurveCdSplit`, and insert
  `grossZagierAlgOptCd_of_split`.
- `FoldCheck.lean`: `ZInQ.EpsSplit.frozenTarget_split` is `frozenTarget` with that change. Output in
  `FoldCheck-output.txt`.
- `autofold.json`: field `hGZ`, one published leaf with kind and flag. autofold.py does not handle binders, as for
  gz-dict2 and hgz-steps.
- `kinds-row.tsv`, `locators-row.md`: proposed rows, not applied.

## 5. Checks (all VERIFIED)

- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GrossZagierSplit`:
  14,283 jobs, no errors (`scratch/eps-splitting/build2.txt`). Both new files also compile under `lake env lean` with
  no errors and no warnings.
- `#discharges` (`scratch/eps-splitting/Discharges.lean`, output `Discharges-output.txt`):

  ```
  DISCHARGES [hGZ] by ZInQ.GZSplit.grossZagierAlgOptCd_of_split
    still assumes: [ZInQ.GZSplit.GrossZagierCurveCdSplit]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 39 open hypotheses, 11491 theorems checked, 52 discharge one
  ```

- `FoldCheck.lean` (`FoldCheck-output.txt`): `[propext, Classical.choice, Quot.sound]` for each of
  `ZInQ.EpsSplit.frozenTarget_split`, `GZSplit.grossZagierAlgOptCd_of_split`,
  `GZSplit.grossZagierCurveCdSplit_of_curveCd`, `EpsSplit.splitType_epsD`, `EpsSplit.quadChar_eq_epsD` and
  `EpsSplit.adjoin_thetaO_eq_top`.
- The new files have no `sorry`, no `axiom`, and no build-time code (`#eval`, `run_cmd`, `syntax`, `notation`,
  macros). Sizes: 7.7 KB and 29.7 KB.

| file | content |
| --- | --- |
| `Contrib/OneProof/GrossZagierSplit/QuadSplit.lean` | `𝓞_K = ℤ[θ]`, `minpoly`, Kummer–Dedekind transfer, three types, `splitType_epsD`, `quadChar_eq_epsD` |
| `Contrib/OneProof/GrossZagierSplit.lean` | leaf `GrossZagierCurveCdSplit`, the equivalence with `GZSch.GrossZagierCurveCd`, `grossZagierAlgOptCd_of_split` |
| `scratch/eps-splitting/QuadInt.lean` | development copy (same proofs, one section) |
| `scratch/eps-splitting/QuadSplit.lean`, `GrossZagierSplit.lean` | copies of the Contrib files |

## 6. What remains

- The integrator's fold (`fold-spec.md`), after or instead of hgz-steps' fold. Both forms are in the build, and the
  bridge goes through hgz-steps' `grossZagierAlgOptCd_of_curve`, so this branch needs hgz-steps' modules (it is
  based on `wip/hgz-steps`).
- Rows for kinds.tsv and locators.md (`kinds-row.tsv`, `locators-row.md`). The GZ locators are not re-read: there is
  no copy on this host.
- Nothing in the `ε_D` identification is left unproved. It covers every negative fundamental discriminant, even
  `D ≡ 0 (mod 4)`, which the leaf does not use.
