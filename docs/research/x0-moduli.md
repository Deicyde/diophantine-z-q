# x0-moduli: the top hypothesis `hX = T5Glue.X0ModuliGalois` split; the canonical model is needed only at the non-isolated (CM) points

Task x0-moduli, 2026-11-15. Branch `wip/x0-moduli` (base 6edf020d, w70). Lean: `scratch/x0-moduli/X0Moduli.lean`,
the contributor-kit file `ZInQKernel/Contrib/OneProof/X0ModuliGalois.lean` (the same body), `#discharges` run in
`scratch/x0-moduli/Discharges.lean` (output `Discharges-output.txt`), autofold spec `scratch/x0-moduli/autofold.json`.
Results log: `scratch/x0-moduli/log.md`.
Marks: **VERIFIED** (compiled, computed, or read in a named source), **STANDARD** (published, exact reference),
**SPECULATIVE**, **UNVERIFIED** (theorem numbers from memory; this host has no network). Model work; one independent model
statement review (§7); no human review.

## 0. Verdict

1. **The requested split into printed leaves over genuine definitions cannot be done in full today.** The three
   printed results that `X0ModuliGalois` glues (review of 2026-11-14) are scheme-theoretic: the coarse moduli
   scheme `Y₀(N)_ℚ` of pairs `(E, C)` (Deligne–Rapoport VI), the `q`-expansion principle on the Tate curve
   (Deligne–Rapoport VII), and the comparison `Y₀(N)(ℂ) ≅ Γ₀(N)\ℍ`. Stating any of them in printed form needs the
   moduli problem of `Γ₀(N)`-structures over a base scheme, coarse moduli spaces, the Tate curve over `ℤ((q))` and
   analytification; none of these is in Mathlib, Tau Ceti or the other libraries surveyed in
   `docs/research/prereq-survey.md`. A Lean "leaf" for them would have to be stated over a structure invented for
   the purpose, which the leaf rule forbids.
2. **What is proved instead (VERIFIED: compiled, axioms `[propext, Classical.choice, Quot.sound]`; `#discharges`
   reports `[hX]` discharged):**

   ```lean
   theorem X0Moduli.x0ModuliGalois_of_leaves (hG : WeierstrassGroupLaw) (hV : VeluCyclic)
       (hR : ShimuraModFnTask.RatX0Rep) (hS : X0ModuliGaloisNonIsolated) : T5Glue.X0ModuliGalois
   theorem X0Moduli.jnConj_of_leaves (hG : WeierstrassGroupLaw) (hV : VeluCyclic) : JNConj
   theorem X0Moduli.x0ModuliGalois_of_split (hR : RatX0Rep) (hJ : JNConj)
       (hS : X0ModuliGaloisNonIsolated) : T5Glue.X0ModuliGalois
   ```

   The moduli and uniformization content of `X0ModuliGalois` (how `σ ∈ Aut(ℂ)` moves `j(τ)` and `j(Nτ)`) is now a
   Lean proof from two textbook statements about `℘` over Mathlib's `PeriodPair`. The `q`-expansion part enters
   through the kernel's existing Prop `RatX0Rep` (`ℚ(X₀(N)) = ℚ(j, j_N)` with a denominator that does not vanish
   at isolated points). The coarse-moduli content is left only at the points `τ` where the plane model
   `(j, j_N)` of `X₀(N)` is not isolated. Those points are CM points, finitely many on `Y₀(N)` for each `N`
   (§3), though in `ℍ` they form whole `Γ₀(N)`-orbits. They are not empty and the consumers need them (shimura-modfn §3: TYZ's class-7 forms at
   `n = 7, 15, 47, …`).
3. **Count.** The split does not lower the strict GLUE count; it raises it (one consequence row becomes four
   non-published rows: `WeierstrassGroupLaw` composite, `VeluCyclic` consequence, `RatX0Rep` composite,
   `X0ModuliGaloisNonIsolated` consequence). It is a refinement, not a fold candidate, and the autofold spec is
   recorded for completeness only (`autofold.py` refuses it: `hX` is a plain argument of `frozenTarget`, §5).
   No statement was changed. `X0ModuliGalois` is not false, vacuous or inert; nothing in this work suggests a
   correction.

## 1. The statement (verbatim copy checked)

`scratch/x0-moduli/Copy.lean`: `X0ModuliGaloisCopy` (verbatim) and `example : X0ModuliGaloisCopy =
T5Glue.X0ModuliGalois := rfl` compile (VERIFIED). In words: `N ≥ 1`, `g` with `IsRatModFn N g`, `σ : ℂ ≃+* ℂ`,
`τ, τ' ∈ ℍ`, `μ`; the moduli coordinates of `τ` are algebraic; `σ(g₂(τ)) = μ⁴g₂(τ')`, `σ(g₃(τ)) = μ⁶g₃(τ')`
(`IsConjModel`); for `N ≥ 2`, some `1 ≤ k < N` with `σ(℘_τ(1/N)) = μ²℘_{τ'}(k/N)` and
`σ(℘'_τ(1/N)) = μ³℘'_{τ'}(k/N)`. Then `σ(g(τ)) = g(τ')`.

## 2. The Props

| Prop | kind | statement (short) | source | why it is or is not the print |
|---|---|---|---|---|
| `X0Moduli.WeierstrassGroupLaw` | textbook; **composite** (strict GLUE) | for `z, w ∉ Λ`: (a) `℘z = ℘w ⇒ z ≡ ±w`; (b) `℘'z = 0 ⇒ 2z ∈ Λ`; (c) chord: `℘(z+w) = λ²/4 − ℘z − ℘w`, `℘'(z+w) = −(λ℘(z+w) + ν)` when `℘z ≠ ℘w`; (d) tangent with `λ = (6℘² − g₂/2)/℘'` when `2z ∉ Λ` | Silverman, *AEC*, GTM 106, Prop. VI.3.6(b) with the group-law formulas III.2.3; Whittaker–Watson §20.3, §20.311 (UNVERIFIED numbers) | Silverman VI.3.6(b) says `z ↦ (℘, ℘')` is a group isomorphism `ℂ/Λ ≅ E_Λ(ℂ)`; III.2.3 gives the chord–tangent formulas for the general Weierstrass form, so (c), (d) need `y ↦ y/2`; Whittaker–Watson print the `℘(z+w)` addition theorem in this normalization, and `℘'(z+w)` follows from collinearity; (a), (b) are injectivity and `E[2]`. Four clauses from two prints: a consequence, not one print. Numerically checked (log 4). |
| `X0Moduli.VeluCyclic` | textbook; **consequence** (strict GLUE) | `N⁴g₂(⟨1,Nτ⟩) = g₂ + Σ_{m=1}^{N−1}(60℘_τ(m/N)² − 5g₂)`, `N⁶g₃(⟨1,Nτ⟩) = g₃ + Σ(140℘³ − 21g₂℘ − 14g₃)` | Vélu, C. R. Acad. Sci. Paris 273 (1971) 238–241; Washington, *Elliptic curves*, Thm. 12.16 (UNVERIFIED) | Vélu prints `A₄ = a₄ − 5t`, `A₆ = a₆ − 7w` algebraically; this is its analytic form for `⟨1/N⟩` (I derived it from Vélu's `t, w` and checked it numerically, log 4). It is also a lattice-sum identity that Mathlib could prove (`℘'' = 6Σ(z−ω)⁻⁴`, `℘'''' = 120Σ(z−ω)⁻⁶`), so it is better treated as glue to be proved. |
| `ShimuraModFnTask.RatX0Rep` (existing, kernel `TYZChain/ModFn.lean`) | **composite** (strict GLUE) | `IsRatModFn N g ⇒ ∃ A, B ∈ ℚ[X,Y]`, `B(j, j_N)g = A(j, j_N)` on `ℍ`, `B(j(τ), j(Nτ)) ≠ 0` at isolated `τ` | Shimura 1971 Prop. 6.9 (`ℚ(X₀(N)) = ℚ(j, j_N)`, the `q`-expansion part); Cox Thm. 11.18 (`Φ_N`); Serre, *Local fields* III §6 (Euler's lemma) (UNVERIFIED) | combination of three textbook facts (shimura-modfn §2, reviewed TRUE there). The printed part is `ℚ(X₀(N)) = ℚ(j, j_N)`; the conductor bound is algebra. |
| `X0Moduli.X0ModuliGaloisNonIsolated` | **consequence** (strict GLUE), same sources as `X0ModuliGalois` | `X0ModuliGalois` with the extra hypothesis `¬ IsIsolated N τ` | Shimura 1971 §6.7; Deligne–Rapoport VI–VII (UNVERIFIED) | a restriction of `X0ModuliGalois` to finitely many CM orbits; still the canonical model, not a print |
| `X0Moduli.JNConj` | GLUE, **proved** (`jnConj_of_leaves`) | under the hypotheses of `X0ModuliGalois`: `σ(j(Nτ)) = j(Nτ')` | — | — |

All new Props are stated over genuine definitions: Mathlib's `PeriodPair`, `weierstrassP`, `derivWeierstrassP`,
`g₂`, `g₃`, and the kernel's `pp`, `scaleH`, `jInv`, `IsIsolated`, `IsRatModFn`, `modCoord`, `IsConjModel`.

## 3. The proof

**Isolated points** (`x0ModuliGalois_isolated`). `RatX0Rep` gives `A, B` with `B(j, j_N)g = A(j, j_N)` and
`B(j(τ), j(Nτ)) ≠ 0`. `σ(j(τ)) = j(τ')` follows from `IsConjModel` once Klein's `j = E₄³/Δ` (the kernel's `jInv`)
is identified with `1728g₂³/(g₂³ − 27g₃²)` of `⟨1, τ⟩` (`jInv_eq_jL`, proved from t5-glue's `G_k = 2ζ(k)E_k` and
Mathlib's `Δ = (E₄³ − E₆²)/1728`). With `σ(j(Nτ)) = j(Nτ')` (`JNConj`), `σ` commutes with evaluation of
`A, B ∈ ℚ[X,Y]`, `σ(B(…τ)) ≠ 0`, and `σ(g(τ)) = σ(A)/σ(B) = g(τ')`. The algebraicity hypothesis is not used.

**`JNConj`** (`jnConj_of_leaves`, VERIFIED).
* `conj_multiples`: by induction on `1 ≤ m < N`, `N ∤ mk`, `σ(℘_τ(m/N)) = μ²℘_{τ'}(mk/N)` and
  `σ(℘'_τ(m/N)) = μ³℘'_{τ'}(mk/N)`. Step `m = 1 → 2`: tangent formula on both sides; `℘'_τ(1/N) ≠ 0` by (b),
  hence `℘'_{τ'}(k/N) ≠ 0`, hence `2k/N ∉ Λ'` (`℘'` is odd and periodic). Step `m → m + 1`, `m ≥ 2`: chord through
  `m/N` and `1/N`; `℘_τ(m/N) ≠ ℘_τ(1/N)` by (a), hence the primed values differ, hence `(m+1)k/N ∉ Λ'` (`℘` is even
  and periodic). The transfer of `λ, ν, x₃, y₃` through `σ` is pure algebra (`slope_transfer`, `tslope_transfer`,
  `x3_transfer`, `y3_transfer`).
* `coprime_of_multiples`: `N ∤ mk` for all `1 ≤ m < N` forces `(k, N) = 1` (take `m = N/(k, N)`).
* `sum_perm`: `m ↦ mk mod N` permutes `{1, …, N−1}`, and `℘_{τ'}(mk/N) = ℘_{τ'}((mk mod N)/N)`.
* `VeluCyclic` at `τ` and `τ'`, `σ` applied term by term, the permutation, and `σ(N^e) = N^e ≠ 0` give
  `IsConjModel σ ⟨1, Nτ⟩ ⟨1, Nτ'⟩ μ`, hence `σ(j(Nτ)) = j(Nτ')`. `N = 1` needs no `k` (empty sums).

**Non-isolated points** are left to `X0ModuliGaloisNonIsolated`. Why they are CM (STANDARD argument): if
`C' ≠ C₀ = ⟨1/N⟩` are cyclic of order `N` with `ι : E/C' ≅ E/C₀`, then `ψ = φ₀^∨ ∘ ι ∘ φ_{C'} ∈ End(E)` has degree
`N²`; if `ψ = ±[N] = ±φ₀^∨∘φ₀` then `φ₀^∨∘(ι∘φ_{C'} ∓ φ₀) = 0`, so `ι∘φ_{C'} = ±φ₀` and `C' = C₀`. So `End(E) ≠ ℤ`,
and `ψ` has norm `N²`, so `|disc End(E)| ≤ 4N²`: finitely many `j`. At such points no `A/B` with
`A, B ∈ ℂ[X, Y]` is regular (shimura-modfn §3 and its review, item 3), so `RatX0Rep`-type arguments cannot reach
them, and lifting to level `NM` does not separate them either (shimura-modfn §3, SPECULATIVE in general).

## 4. What would remove `X0ModuliGaloisNonIsolated` (not done; SPECULATIVE route)

Use separating functions that, like `j_N`, can be computed from `(E, C)`: the Fricke symmetric functions
`s_r(τ) = (g₂g₃/Δ)^r Σ_{m=1}^{N−1} ℘_τ(m/N)^r` (and `(g₂²/Δ)^r Σ ℘²ʳ`, `(g₃/Δ)^r Σ ℘³ʳ` near `j = 1728, 0`).
They lie in `ℚ(X₀(N))`. `σ` acts on their values through the hypothesis exactly as in `conj_multiples`, and for
`j ≠ 0, 1728` they separate the fibre of `Y₀(N) → Y(1)`: `x(c)` determines `±c`, so the multiset of `℘(c)`,
`c ∈ C \ 0`, determines `C`. What is missing is a `RatX0Rep` for a primitive element `h = Σ λ_r s_r`: a
representation `B(j, h)g = A(j, h)` with `B(j(τ), h(τ)) ≠ 0` wherever the values of `h` on the fibre are
distinct. That is the same Euler-lemma argument, applied to the minimal polynomial of `h` over `ℚ(j)`. It also
needs the rational `q`-expansions of the `s_r`, from the `q`-expansion of `℘` at `N`-torsion points (Silverman,
*Advanced topics*, I.6.2, UNVERIFIED), and a separate treatment of `j = 0, 1728`. This would replace
`X0ModuliGaloisNonIsolated` by textbook statements and glue, but the glue (minimal polynomials over `ℚ(j)`,
cosets of `Γ₀(N)` in `SL₂(ℤ)`) is a large Lean project.

## 5. Deliverables and checks

* `scratch/x0-moduli/X0Moduli.lean`, `ZInQKernel/Contrib/OneProof/X0ModuliGalois.lean` (the same body; module
  docstring; imports `ZInQKernel.Contrib.OneProof.RingClassLattice`, which defines the statement, and
  `ZInQKernel.Contrib.TYZChain.ModFn`, which defines `RatX0Rep`; not `OneProof.Main`). `lake build
  +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.X0ModuliGalois`: OK (VERIFIED).
* `#discharges` (VERIFIED, `scratch/x0-moduli/Discharges-output.txt`):

  ```
  DISCHARGES [hX] by X0Moduli.x0ModuliGalois_of_leaves
    still assumes: [X0Moduli.WeierstrassGroupLaw,
   X0Moduli.VeluCyclic,
   ZInQ.Contrib.TYZGenus.ShimuraModFnTask.RatX0Rep,
   X0Moduli.X0ModuliGaloisNonIsolated]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [hX] by X0Moduli.x0ModuliGalois_of_split
    still assumes: [ZInQ.Contrib.TYZGenus.ShimuraModFnTask.RatX0Rep, X0Moduli.JNConj, X0Moduli.X0ModuliGaloisNonIsolated]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 68 open hypotheses, 951 theorems checked, 3 discharge one
  ```
  (The third line of the full output is an existing contribution, `GRCountX6.prop56X6_of_r5fpCount`.)
* `scratch/x0-moduli/autofold.json`: discharge `hX` by `x0ModuliGalois_of_leaves` with the four Props as leaves
  (kinds composite, consequence, composite, consequence). `autofold.py --dry-run` (VERIFIED):
  `autofold: not a field of the current bundles: ['hX']`. `hX` is a plain argument of `frozenTarget`, so a fold
  would be a hand edit of `Main.lean`, as for `hS` in gt-ringclass. Under the strict rule it would raise the GLUE
  count from 1 to 4, so it is not proposed.
* Numerical checks (VERIFIED, PARI/GP 2.x through cypari2, 40–50 digits; log 4): `VeluCyclic` at 5 pairs
  `(τ, N)`; clauses (c) and (d) of `WeierstrassGroupLaw` at 2 points each.

## 6. What remains

* `X0ModuliGaloisNonIsolated`: the canonical model at the non-isolated CM points (route in §4).
* `RatX0Rep`: printed core `ℚ(X₀(N)) = ℚ(j, j_N)` (Shimura Prop. 6.9) plus `Φ_N` and Euler's lemma; Mathlib has
  neither modular polynomials nor function fields of modular curves.
* `VeluCyclic`: provable from Mathlib's lattice sums (glue); not attempted.
* `WeierstrassGroupLaw`: the addition theorem for `℘` is not in Mathlib (its `Weierstrass.lean` has `℘`, `℘'`,
  `℘'² = 4℘³ − g₂℘ − g₃`, periodicity and parity); provable by Liouville's theorem for elliptic functions, which
  Mathlib does not have yet.

## 7. Review

Independent statement review: an AI subagent, read-only, no Lean, 2026-11-15; no human review. It worked from
Mathlib's definitions, not from the docstrings. Verdicts:

1. `WeierstrassGroupLaw`: **TRUE**, all four clauses. The signs and the factor `1/4` are right. No clause divides
   by zero: in (c), `℘z ≠ ℘w` already gives `z + w ∉ Λ`; in (d), `℘'z ≠ 0` follows from (b).
2. `VeluCyclic`: **TRUE**. The reviewer rederived every constant from lattice sums (`℘'' = 6℘² − g₂/2`,
   `℘'''' = 120℘³ − 18g₂℘ − 12g₃`) and matched the result with Vélu's `A₄ = a₄ − 5t`, `A₆ = a₆ − 7w`. The case
   `N = 1` is fine.
3. `X0ModuliGaloisNonIsolated`: **TRUE**. It is a verbatim restriction of `X0ModuliGalois` and is not vacuous:
   `N = 2`, `τ = i`, `σ = id`, `k = 1` satisfy every hypothesis, since `j(i/2) = j(2i)`. The CM argument is
   correct. "Finitely many" holds on `Y₀(N)`, not in `ℍ`; the docstring and report say `Y₀(N)`. The reviewer's
   caveat: the remaining Prop is still the canonical model at CM points, so it is a restriction, not a change of
   kind.
4. Logical gaps: **none**. `IsIsolated` is used in the direction `RatX0Rep` supplies, and the nonvanishing at
   `τ'` comes from `σ`.
5. Attribution: **accurate as a consequence**, with one fix, now applied in both Lean files and in §2. Silverman
   III.2.3 is for the general Weierstrass form, so (c) and (d) need `y ↦ y/2`. Whittaker–Watson §20.3 prints the
   addition theorem in this normalization, and `℘'(z + w)` follows from collinearity. Duplication is §20.311.
