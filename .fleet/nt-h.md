# nt-h report: making the height hypothesis H cheaper

Deliverable: `docs/research/nt-h.md`. Scripts and outputs: `scratch/nt-h/` (`slack.py`,
`quotients.py`, `genus2cusp.py`, each with an `.output.txt`).

## Summary

1. **What the consumers need (VERIFIED from the Lean proofs).** `SixContactMin` is used at one
   adversarial rational number per consumer: the main-branch value `t`
   (`Assembly.ratHeight_le_bound_of_test`) and the certificate slope `t`
   (`Mult.slope_height_le_of`). The precision use accepts any computable bound. The
   multiplication use accepts any exponent `e ≤ 25 - 2^{-2^{65535}}` and any constant with
   `log₂ A = D^x`, `x < 2^{56525}` (now `x = 7`), but no super-polynomial shape. Averages,
   bounds outside a thin set and cheap restrictions of the slopes are all useless, because
   soundness is worst-case and every cheap restriction leaves twists of a compact curve of genus
   `≥ 2`. A rank-zero-quotient idea is vacuous: in all 131 × 15 cases tested, the image of a
   point in an elliptic quotient of its twist has infinite order.
2. **Changes of construction (§3 of the note).**
   - *Cusp lemma*: each cusp is approached at a set of primes of positive density, where the
     fibre is bad for every positive valuation, even or odd. Parity tests never see these
     primes, and integrality tests at finitely many primes do not help.
   - Inside the present construction, the fibres *as genus-two curves* degenerate at every prime
     with a positive contact valuation (`J₁₀ = j³` vanishes exactly at the contacts; 19/19
     inputs tested). So the Baker-accessible genus-two Shafarevich theorems cannot be used.
   - *Affine-moduli lemma*: the parity-to-good-reduction property forces a cusp-free family, so
     the moduli image is a complete curve. All moduli spaces with Baker or `S`-unit effective
     Shafarevich theorems are affine, so they carry only isotrivial families. QM surfaces over a
     rational quaternionic Shimura curve are the cheapest remaining choice.
   - *Correction to earlier notes*: rs-global C1 does not exclude a test enforcing positivity
     *relative to a controlled label integer K* ("`v_p(t - c) > 0 ⇒ p ∣ K`"), because true
     inputs never need `K = ±1`. Such a test would let the Stewart–Yu `S`-unit bound (Baker)
     replace H entirely. It needs an existential local device that sees positive valuations at
     all primes, and none is known.
3. **An older modularity input (§4).** Serre's 1987 pigeonhole at varying `ℓ` works with
   Khare–Wintenberger's strong form of Serre's conjecture. At infinitely many large `ℓ ∉ T`,
   `r̄_λ` is absolutely irreducible (mod-`ℓ` Faltings), odd, of weight 2 (finite flat at `ℓ`)
   and of level `≤ QM²` (the manuscript's local bounds hold for every `ℓ ≠ p`). Pigeonhole over
   the finitely many newforms of weight 2 and level `≤ QM²` then gives `r_λ ≅ ρ_{f,λ}`. This
   replaces Pan (A011) and removes A009, A010 and Conrad's local algebraicity. Carayol moves
   inside the citation. Constants are unchanged. Depth is unchanged (modularity lifting
   underlies both theorems), but the input becomes a 2009 theorem. Langlands–Tunnell with 3-adic
   lifting, level lowering alone, and modular parametrizations of `X⁶/W` do not apply, since the
   fibres are points of the curve, not quotients of its Jacobian.

## Ranking

| # | Route | Payoff | Chance |
| --- | --- | --- | --- |
| 1 | Serre's argument at large `ℓ` in place of Pan | medium: removes Pan, A009, A010 and Conrad | high |
| 2 | Route 1 combined with h-leaves (NoCM, R5.1) | small extra: no `p`-adic Hodge theory left in H | high |
| 3 | Consumer-shaped hypotheses `H_P^c`, `H_M^c` in Lean | small (trust boundary only) | high |
| 4 | A relative positivity test (Pos_K) | would remove H (Stewart–Yu replaces it) | very low |
| 5 | Effective Shafarevich for QM surfaces without modularity | removes modularity from H | very low |
| 6-7 | Thin sets, rank-zero quotients, elliptic or genus-two families | — | nil (settled) |

## Open questions

- Exact statements and numbers in Khare–Wintenberger 2009 (strong form at `ℓ > 2`, level
  `N(r̄)`, weight `k(r̄)`), Raynaud 1974 (finite flat descent for `e = 1`), Serre 1987 §2.8
  (weight 2 for finite flat representations) and a citable mod-`ℓ` Faltings theorem. All are
  UNCHECKED here.
- Is there any existential local device detecting `v_p(x) > 0` at all primes relative to a
  label integer? A negative theorem (a formal reason why relative positivity cannot be
  existential) would also be useful, since it would close route 4.
- Liu's potential-good-reduction criterion for genus two: pin the theorem number used in §3.3.

## Suggested follow-up tasks

1. **ser-ell**: audit route 1. Read Khare–Wintenberger 2009 and the other sources of §4.2,
   write audit records for steps 1-7, and check that no extra hypothesis appears (residual image,
   `ℓ ∤ N(r̄)`, `ℓ > 2`). Success: every step matched to a numbered statement.
2. **leaves-v2**: redo the final table of h-leaves §5.1 with route 1, and record I1/I2 as audit
   records.
3. **pos-k**: a focused study of relative positivity. Either construct an existential test for
   "`v_p(t) > 0 ⇒ p ∣ K` for all large `p`" (complete on `(n, F(n))`), or prove that the parity
   and quadratic-form devices, and their compositions, cannot express it.
