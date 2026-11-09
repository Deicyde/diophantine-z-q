# Referee report on Lemma P and the modified completeness argument of `nt-22p.md`

Scope: §3.2 of `docs/research/nt-22p.md` (Lemma P, field 2′, the modified choice of the witness
`q`) and §3.3 (Proposition AP and its remarks), checked against the 11/5 manuscript
`diophantine_zq.tex` (lines 1170–1190 and 1700–1758) and against the Lean definitions
`ZInQ.Mult.GoodSlope`, `slope_complete`, `pole_input_valuations`, `weak_approx_q`,
`tests_integral_old` and `ZInQ.PoleCompleteness`. Proposition D, Green–Tao 2008 and §4 of the note
are outside this report, except where §3.3 depends on them.

Notation is that of the note: `t = u/v` in lowest terms, `e = v_ℓ(v)`, `R₀ = ηF(t)/(t − 1)⁸`,
`a = 1 − R₀q²`, `α = v_ℓ(a)`, `R = ℓ₀²a²R₀`, `C_{gj} = D_{gj}/(R₀^{k_j}(t − 1)^{k_j+1})`,
`W_g = ∏_j(1 + RC_{gj}²)`, `Θ = Tr Σ_g W_g^{−1}`, `B = R/Θ²`, `E_ℓ = v_ℓ(ℓ₀)`.

## Verdict

**Proved after the listed repairs.** Lemma P (1)–(3), the modified completeness argument with
field 2′, Proposition AP and Remark 3 (Lemma P is needed only on `S₀`) are correct. I checked
each step by hand against the manuscript and the Lean source. An independent exact computation
confirms Lemma P(1) at `ℓ = 2` and Lemma P(3) on 30 samples, and a negative control shows that
its threshold is really used. None of the repairs below changes the argument. They correct one
false numerical statement (about `e = 1, 2` at the prime 2) and one wrong constant (`K_A`), drop
redundant hypotheses, and correct the plan of Lean changes in §5 of the note. That plan is
incomplete and partly wrong about which lemmas change, but it is correct about which lemmas need
new mathematics.

## Findings

| # | Item | Verdict | Severity |
| --- | --- | --- | --- |
| 1 | Lemma P(1): `v_ℓ(R₀) = 2e`, `v_ℓ(t − 1) = −e`, `R₀ ∈ ℚ_ℓ^{×2}` | CORRECT | — |
| 2 | Lemma P(2): `v_ℓ(1 − R₀q²) ≥ N` on a non-empty open set | CORRECT | — |
| 3 | Lemma P(3): `v(RC²) ≥ 2α − 46e`, `v_ℓ(Θ) = v_ℓ(12)`, `v_ℓ(B) ≥ 4` | CORRECT | — |
| 4 | Test integrality `v_𝔩(D_{gj}) ≥ 0` above `S_b` is independent of `t` | CORRECT | — |
| 5 | The prime 2: `e ≥ 3` suffices; for `e = 1, 2` | CORRECT; the note's control statement understates | minor |
| 6 | Redundant hypotheses of Lemma P (seven numerators prime to `ℓ`) | not an error | cosmetic |
| 7 | Field 2′ and the modified choice of `q` (all five kinds of places) | CORRECT | — |
| 8 | Proposition AP (lowest terms, signs, fields 1, 2′, 3, 4) | CORRECT | — |
| 9 | Remark 1: the constant in `K_A ≈ |A| + 71` | wrong constant; harmless | cosmetic |
| 10 | Remark 3: Lemma P only on `S₀ = {2, 3, 5, 7, 13}` | CORRECT; can be strengthened | — |
| 11 | Plan of Lean changes (§3.2, §5 Route 1) | incomplete; partly wrong | minor |
| 12 | Size of the poles actually needing Lemma P | observation | — |

Details follow, in the order of the table.
