# h29-split: `TYZLemma29Mod2` from TYZ Lemma 2.9 and Proposition 2.3 in printed form

Task h29-split, 2026-11-15. Branch `wip/h29-split` (base 6edf020d, leaf-fold18). Results log:
`scratch/h29-split/log.md`. Lean: `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` (the contribution) and
`scratch/h29-split/H29Split.lean` (the same plus the inertness and Theorem 1.1 checks). Discharge check:
`scratch/h29-split/DischargesH29.lean`, output `DischargesH29-output.txt`. Autofold spec:
`scratch/h29-split/autofold.json`. Numeric checks: `scratch/h29-split/checks.py`.
Marks: **VERIFIED** (compiled, computed, or read in the named source at the line numbers given),
**STANDARD** (published, exact reference), **SPECULATIVE**, **UNVERIFIED** (from memory; this host has no network).
TYZ = Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1, Asian J.
Math. 21 (2017). `Lnnnn` are line numbers of `~/tyz-src/Period7.tex`, **read for this task**. Nothing from it is
copied here beyond a few words. Model work, no human review.

## 0. Main result

**The top hypothesis `h29 = ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` of `ZInQ.OneProof.frozenTarget` is proved
from four statements over genuine definitions: TYZ Lemma 2.9 and Proposition 2.3 in printed form, the
existence of TYZ's test vector, and Legendre's three-square theorem in the form TYZ cite** (VERIFIED: compiled,
`#discharges` output below, axioms `[propext, Classical.choice, Quot.sound]`):

```lean
theorem ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedLeaves_threeSquares
    (hL : LegendreJonesPall) (hfx : TYZTestVectorExists)
    (h29 : TYZLemma29Printed) (h23 : TYZProp23Printed) : TYZLemma29Mod2
theorem ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedLeaves
    (hτ : TYZTauExists) (hfx : TYZTestVectorExists)
    (h29 : TYZLemma29Printed) (h23 : TYZProp23Printed) : TYZLemma29Mod2
theorem ZInQ.Contrib.TYZDecomp.H29Split.tyzTauExists_of_legendreJonesPall
    (h : LegendreJonesPall) : TYZTauExists
```

```
DISCHARGES [h29] by ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedLeaves
  still assumes: [ZInQ.Contrib.TYZDecomp.H29Split.TYZTauExists,
 ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists,
 ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29Printed,
 ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [h29] by ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedLeaves_threeSquares
  still assumes: [ZInQ.Contrib.TYZDecomp.H29Split.LegendreJonesPall,
 ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists,
 ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29Printed,
 ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 66 open hypotheses, 1279 theorems checked, 5 discharge one
```

(The other three lines of the output are contributions already folded in.) The leaves are stated over TYZ's
objects as Lean definitions, not over parameters: `B = ℍ[ℚ]`, `O_B` (Hurwitz order), `B̂ = ℍ[𝔸ᶠ_ℚ]`, the embedding
`τ`, `τ̂ : 𝔸ᶠ_{K_n} → B̂` (through Tau Ceti's base change of finite adeles), `R̂_n`, `K_{n,2}^×`, `U_n`, `π_ℤ^{U_n}`
(pinned by its Hecke eigenvalues), the test vector `f_n`, the class group `Cl_n` read adelically (Tau Ceti's
`toClassGroup`), and the genus period `Q(n)`. The glue (mod-2 reduction, the "therefore" of Proposition 2.3, the
class-group step) is proved in Lean.

The previous version of this task (first run, when the source was not on the host) stated Lemma 2.9 and
Proposition 2.3 with `Q(n)` (or `f_n`) as a parameter, and proved that version **inert**: some `Q` satisfies both
iff `TYZLemma29Mod2` holds (`exists_printedQ_iff`, `exists_printedF_iff`, still in the scratch file). The genuine
definitions of this run remove that problem.

## 1. The leaves

| Lean name | Source (read) | Kind | Content |
|---|---|---|---|
| `TYZLemma29Printed` | TYZ Lemma 2.9, L1062–1066 | LEAF (printed form, restricted) | for squarefree `1 < n ≡ 1, 3 (mod 8)`, every admissible `τ` and every generator `f` of `π_ℤ^{U_n}`: for every sign choice `ℓ` of `𝓛` there are `ε(d) = ±1` and `w ∈ {1; 3 at n = 3}` with `w·Σ_{n=d₁d₂, d₂≡1 (8)} ε 𝓛(d₁)𝓛(d₂) = Q(n)` (non-ordered pairs) |
| `TYZProp23Printed` | TYZ Proposition 2.3, L580–586 | LEAF (printed form, restricted) | same `n, τ, f`: `f(h²)` is odd for every `h ∈ B̂^×` |
| `LegendreJonesPall` | Legendre's three-square theorem; for `4 ∣ c`, Jones–Pall, Acta Math. 70 (1939) 165–191, Thm 5, as cited by TYZ L533 (bib L3290–3292; Jones–Pall not read, UNVERIFIED) | LEAF (classical) | a squarefree `n ≡ 1, 3 (mod 8)` is `a² + b² + c²` (`a, b, c ∈ ℤ`), with `4 ∣ c` if `n ≡ 1 (8)`; checked on 30 random squarefree `n < 10⁵` (`checks.py`, VERIFIED) |
| `TYZTauExists` | TYZ §2.1, L527–534 | intermediate, **proved** from `LegendreJonesPall` (`tyzTauExists_of_legendreJonesPall`) | for squarefree `n ≡ 1, 3 (mod 8)` an embedding `τ : ℚ(√−n) → B` with `τ(O_K) ⊂ O_B` and, if `n ≡ 1 (8)`, `τ(√−n) = ai + bj + ck`, `n = a²+b²+c²`, `4 ∣ c` |
| `TYZTestVectorExists` | TYZ §2.1, L542–550, with Theorem 2.6 (L809–840) at `χ = 1` | LEAF, flagged pending reading | for every admissible `τ`, `π_ℤ^{U_n}` (as defined by `InPiZ`) has a generator. TYZ print "free of rank 1"; the leaf is the existence half. Flag: `InPiZ` defines `π^{U_n}` as the `a_p(E)`-eigenspace of the `U_n`-invariant forms, which equals TYZ's `π^{U_n}` by strong multiplicity one and Jacquet–Langlands (STANDARD), not by TYZ's text |

Restrictions (each a weakening of the print): only `n ≡ 1, 3 (mod 8)` (TYZ §2 covers `1, 2, 3`, L499); Lemma 2.9
only for `n > 1`; the factor `w` (§2, "The factor `w_K`").

## 2. Statement checks (all VERIFIED by reading the lines named; details in the log)

* **Numbering.** `\newtheorem{thm}{Theorem}[section]` with lemma/proposition/corollary/definition on the same
  counter (L244–252). Section 2 (from L496): Thm 2.1 L554, Thm 2.2 L571, **Prop 2.3 L580**, Thm 2.4 L613, Lemma 2.5 L646,
  **Thm 2.6 L809** (label `thm2.3`), Definition 2.7 L842, **Lemma 2.8 L1009** (symmetry), **Lemma 2.9 L1062**.
* **Lemma 2.9 index set.** Non-ordered decompositions `n = d₁d₂`, `d₁, d₂ > 0`, `d₂ ≡ 1 (mod 8)`. For
  `n ≡ 3 (8)` the other factor is `≡ 3`, so the pairs are indexed by the divisors `d ≡ 1`; for `n ≡ 1 (8)` both
  factors are `≡ 1` and distinct (squarefree, `n > 1`), indexed by the smaller one (`pairIdx`). Matches the
  target's two sums.
* **Signs.** `ε(d₁, d₂) = ±1` vanish mod 2; a sign change of `𝓛(d)` is absorbed by `ε`, so the leaf quantifies
  over every sign choice `ℓ` with `ℓ² = 𝓛²` (the `lcalSq` pin of TYZDecomp §2).
* **The factor `w_K` (finding B1 of rv-nt-tyz, confirmed).** TYZ's proof of Lemma 2.9 (L1068–1077) combines
  the non-ordered form `Σ P = 2^{h₂−δ} Q(n)` with Theorem 2.1, `P = ±2^{k−a} w_K 𝓛(d₁)𝓛(d₂)` (`2w_K = #μ(K)`,
  L557–558), and `h₂ + 1 = #` primes dividing the discriminant (L993). For odd `n`: `n ≡ 1 (8)`, disc `−4n`,
  `h₂ = k`, `δ = 1`; `n ≡ 3 (8)`, disc `−n`, `h₂ = k − 1`, `δ = 0`. Both give `w_K Σ ε𝓛𝓛 = Q(n)`, not the printed
  `Σ ε𝓛𝓛 = Q(n)`, at `n = 3` (`w_K = 3`). Either Lemma 2.9 or Theorem 2.1 is misprinted there. The leaf admits
  `w = 3` at `n = 3` (implied by both readings); `3` is odd, so the mod-2 reduction is unaffected.
* **Proposition 2.3.** First assertion `f_n((B̂^×)²) ⊂ 1 + 2ℤ` is the leaf; the "therefore" `Q(n) ≡ g(n)` is glue,
  proved: a class `t ∈ 2Cl_n` is `s²` up to `K^×` and `Ô_K^×` (Tau Ceti's `ker_toClassGroup`), `f_n` is left
  `B^×`- and right `U_n`-invariant with `τ(K^×) ⊂ B^×`, `τ̂(Ô_K^×) ⊂ R̂_n^× ⊂ U_n`, so `f_n(t)` is odd and
  `Q(n) ≡ #2Cl_n = g(n)` (`odd_on_sqClasses`, `genusPeriod_mod_two`, `card_sqClasses`).
* **`τ`** (L527–534). `τ(O_{K_n}) ⊂ O_B`; for `n ≡ 1 (8)` the `4 ∣ c` choice, which Lemma 2.8 and the proof of
  Proposition 2.3 (L1134–1160, `χ₀(g) = 1`) use. The leaves are `∀ τ` admissible, which is what "Fix an
  embedding" proves.
* **`π_ℤ^{U_n}`, `U_n`, `f_n`** (L536–550): `π` the Jacquet–Langlands transfer of the newform of `E : y² = x³ − x`
  (level 32), inside `C^∞(B^×\B̂^×/Q̂^×)`; `π_ℤ` its integer-valued elements; `U_n = R̂_n^× K_{n,2}^×`,
  `R_n = O_{K_n} + 4O_B`; `f_n` a `ℤ`-generator, up to sign. Theorem 2.6 at `χ = 1`: with
  `U₂ = ℤ₂^×(1 + 4O_{B,2})` (L603–605), `R_{n,2}^× = O_{K,2}^×(1 + 4O_{B,2})`, so `U_n = U·K₂^×` and `π^{U_n}` is
  Theorem 2.6's `π^{U,1}`, one-dimensional; root number `+1` holds for `n ≡ 1, 2, 3`; `K₂ = ℚ₂(√−3)` for
  `n ≡ 3`, `(ℚ₂(√−1), +1)` for `n ≡ 1`.
* **Hecke normalization** (computed, `checks.py`, VERIFIED): the Lean set `hurwitzNorm p` has `24(p + 1)` elements
  for `p = 3, 5, 7, 11, 13`, and `apE p = p + 1 − #E(𝔽_p)` (`a₅ = −2`, `a₁₃ = 6`). Each norm-`p` Hurwitz
  quaternion lies in `O_{B,p}^× ϖ O_{B,p}^×`, and two give the same right coset iff they differ by one of the 24
  units of `O_B` (listed at L674), so `Σ_α f(x α_p) = 24 (T_p f)(x)`; `T_p` acts on `π` by `a_p(E)` (STANDARD,
  e.g. Gross, *Heights and the special values of L-series*, CMS Conf. Proc. 7 (1987), §4, UNVERIFIED section).
* **A remark on Theorem 2.1 (not used).** Read literally for `n ≡ 3 (8)` and `(d₁, d₂) ≡ (1, 3)`, "P ≠ 0 only if
  `d₂ ≡ 1 (mod 8)`" conflicts with `χ_{d₁,d₂} = χ_{d₂,d₁}` (L994–995); its proof (L983–984) treats only
  `d₂ ≡ −1`. Lemma 2.9's sum (pairs with one factor `≡ 1`) is not affected.

## 3. The genuine definitions (Lean, `TYZLemma29Mod2.lean` §5)

| Lean | TYZ object |
|---|---|
| `ℍ[ℚ]`, `IsHurwitz` | `B` (L520–523), `O_B = O_B' + ℤζ` (L524–525) |
| `AQ = FiniteAdeleRing (𝓞 ℚ) ℚ`, `ℍ[AQ]`, `qι` | `𝔸ᶠ_ℚ`, `B̂ = B ⊗ 𝔸ᶠ_ℚ`, `B → B̂` |
| `hurwitzHat` | `Ô_B = O_B ⊗ Ẑ` |
| `AdmissibleTau n τ` | `τ : K_n → B` (L527–534) |
| `tauHat`, `tauHatU` | `K̂_n = 𝔸ᶠ_{K_n} ≅ 𝔸ᶠ_ℚ ⊗ K_n → B̂` (`TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv`) |
| `RnHat`, `RnUnits` | `R̂_n = τ̂(Ô_K) + 4Ô_B`, `R̂_n^×` (L543–544) |
| `K2Units`, `Un` | `K_{n,2}^×` (component 1 off 2, commuting with `τ(√−n)`), `U_n` (generated subgroup) (L543) |
| `eAt`, `ιAt`, `apE`, `hurwitzNorm`, `quatOf` | `α ↦ α_p ∈ B_p^× ⊂ B̂^×`, `a_p(E)`, Hurwitz quaternions of norm `p` |
| `InPiZ`, `IsTestVector` | `π_ℤ^{U_n}`, `f_n` (L545–563) |
| `clLift`, `sqClasses`, `genusPeriodTV` | `Cl_n = K^×\K̂^×/Ô_K^×` (Tau Ceti `FiniteAdeleRing.toClassGroup`), `2Cl_n`, `Q(n)` (L566–568) |

`f_n` is a function `ℍ[AQ] → ℤ` whose values off `B̂^×` are never used (every condition quantifies over units).

## 4. Glue proved (Lean)

From the three-square statement to `τ` (`tyzTauExists_of_legendreJonesPall`): `tauOf` (`√−n ↦ ai + bj + ck`
through Mathlib's `QuadraticAlgebra.lift`), `trace_norm_int` (an integral `x = u + v√−n` has `2u ∈ ℤ` and
`u² + nv² ∈ ℤ`, using the conjugation `star`), `int_of_sqfree_mul_sq` (`n w² ∈ ℤ`, `n` squarefree, gives `w ∈ ℤ`),
`parity_one`, `parity_three`, `odd_of_three` (mod-4 parity; for `n ≡ 3 (8)` the representation has `a, b, c` odd),
`admissible_tauOf` (`τ(O_K) ⊂ O_B`: integer coordinates, or all in `½ + ℤ`). Then:
`tyzLemma29Mod2_of_printed` (mod-2 reduction for any `Q`), `tyzLemma29Mod2_of_printedF`, `genusPeriod_mod_two`,
`card_sqClasses`, `tauHat_algebraMap` (`τ̂(k) = τ(k)` for `k ∈ K`), `tauHatU_mem_Un`, `odd_on_sqClasses`, `tvFun`,
`tyzLemma29Mod2_of_printedLeaves`. All `[propext, Classical.choice, Quot.sound]` (VERIFIED). The scratch file also
keeps run 1's checks: `exists_printedQ_iff`, `exists_printedF_iff` (with `Q` unpinned the pair is the target),
`thm11Mod2_iff` (given `h11`, `TYZThm11Mod2 ↔ TYZLemma29Mod2`).

## 5. Folding (for the integrator)

`h29` is a plain argument of `frozenTarget`, not a bundle field, and `autofold.py` folds bundle fields only:
`autofold.py scratch/h29-split/autofold.json --dry-run` answers `not a field of the current bundles: ['h29']`
(VERIFIED). The spec lists the proof term `tyzLemma29Mod2_of_printedLeaves_threeSquares` and its four leaves
(kind `published`; `TYZTestVectorExists` flagged pending reading, `LegendreJonesPall` flagged locator UNVERIFIED)
in autofold's format, for a by-hand fold: in `Main.lean`, import
`ZInQKernel.Contrib.OneProof.TYZLemma29Mod2`, replace the argument `(h29 : TYZLemma29Mod2)` by
`(hLJP : H29Split.LegendreJonesPall) (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29Printed)
(hP23 : H29Split.TYZProp23Printed)` and the use of `h29` by
`(ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedLeaves_threeSquares hLJP hfx hL29 hP23)`; replace the
kinds.tsv row `frozenTarget h29 composite` by four rows (`tyzLemma29Printed`, `tyzProp23Printed` LEAF unread;
`legendreJonesPall` LEAF, locator UNVERIFIED; `tyzTestVectorExists` GLUE pending reading); add locator rows for
L1062–1066, L580–586, L533 (Jones–Pall Thm 5), L542–550/L809–840.

## 6. What remains

* `LegendreJonesPall` is elementary number theory and a natural crowd target; Mathlib 4.35 has no three-square
  theorem (searched). Jones–Pall's Theorem 5 was not read (no network).
* `TYZTestVectorExists`'s flag: the identification of `π^{U_n}` by Hecke eigenvalues is standard but not TYZ's
  wording; an alternative pin uses TYZ's Lemma 2.5 (`B^×\B̂^×/Q̂^×U ≅ O_{B,2}/(ℤ₂ + 2O_{B,2})`, 8 classes) and
  `π^U = 𝒜₀^U` (orthogonal to `χ ∘ det`), which TYZ use (L715–730), at the cost of reading more of TYZ.
* No human has read the leaves against the print. A second model read (a fresh agent, given the code and the
  source lines, not this report's conclusions) found no false, vacuous or too-strong leaf; its notes (the
  Hecke bridge is unprinted; TYZ's citations cover `n ≡ 1 (8)` only, `n ≡ 3` being Gauss/Legendre with odd
  `a, b, c`) are reflected in the docstrings.
