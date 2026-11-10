# ser-ell report: audit of route 1 of nt-h §4.2 (Serre's argument at large ℓ)

Deliverable: `docs/research/ser-ell.md`. Script: `scratch/ser-ell/checks.py`, output in
`checks.output.txt`. Log: `scratch/ser-ell/log.md`.

## Verdict

**Proved after the listed repairs, with the constants unchanged.** Route 1 replaces Pan's theorem
(A011, modular part) and removes the de Rham comparison (A009), Berger (A010), Conrad's local
algebraicity and the separate Carayol leaf. Li, Shimura and the Faltings Hom theorem (A063) stay.
The transfer (lines 858-966) needs only a weight-2 newform `f` with `N_f ≤ QM²` sharing a Tate
constituent with `A`, and route 1 supplies exactly that.

The repaired argument still rests on primary statements that could only be read through published
restatements: Serre's conjecture in its strong form (Khare–Wintenberger I and II, and Kisin),
Raynaud's inertia exponents for `e = 1`, and Serre's weight recipe. These are marked UNCHECKED.
Masser–Wüstholz was read as restated in Zywina, Theorem 2.4.

## Step by step

| Step | Status | Source matched |
| --- | --- | --- |
| 1 residual abs. irreducibility | CORRECT | Zywina arXiv:1910.14171 Thm 2.4 (MW95); `End(A_{L'}) = O`, `O/ℓ = M₂(𝔽_ℓ)` (disc 6 computed) |
| 2 oddness | CORRECT | manuscript lines 742-752 |
| 3 weight 2 | CORRECT after repairs F2-F4 | Raynaud §2, §3.4; Serre §2 via BDJ Thm 3.17 (UNCHECKED primaries) |
| 4 level `≤ QM²` | CORRECT, simpler proof | manuscript lines 812-857 apply verbatim to `r̄_λ` |
| 5 Serre's conjecture | CORRECT as an application; citation incomplete (F1) | KW I, KW II and **Kisin 2009** (UNCHECKED; restated by Gee, Dieulefait, BDJ) |
| 6 pigeonhole | CORRECT after bookkeeping (F6) | elementary |
| 7 identification and transfer | CORRECT | Chebotarev, Brauer–Nesbitt, Shimura, A063 |

None of the cited theorems carries a hypothesis that fails. Serre's conjecture has no
residual-image condition. `ℓ ∤ N(r̄)` holds by definition, and `ℓ > 2` is automatic (`ℓ > 324`).

## Findings

- **F1 (moderate).** Khare–Wintenberger alone does not cover even conductor. Kisin, Invent. Math.
  178 (2009) 587-634, is needed, and `N(r̄_λ)` can be even (`2 ∈ T`, and `β` may ramify at 2). If
  the printed statement is the weak form, the classical level and weight optimization (Ribet,
  Carayol, Diamond, Edixhoven, Mazur's principle) is also part of the citation.
- **F2 (minor).** Step 3 works over `O_{L_v}`, where the representation is the Tate action twisted
  by `β^{-1}`. It should use `L'`, which is unramified at `ℓ ∉ T`.
- **F3 (minor).** Step 3 appeals to Raynaud's uniqueness (§3.3) for a descent to `ℤ_ℓ` that is
  unnecessary, since `k(ρ̄)` depends only on `I_ℓ`. It omits what is needed: subquotient closure,
  Raynaud's inertia exponents (§3.4), and "finite flat ⇒ peu ramifiée".
- **F4 (minor).** The determinant claim of step 3 is unproved. Repair: `det r̄|_{I_ℓ} = ω·η`, with
  `η` quadratic and the value in `{1, ω, ω²}`, forces `η = 1` for `ℓ > 3`.
- **F5 (minor).** Step 4 cites "Serre 1987, §1.2" for "reduction does not raise the conductor".
  The attribution is unconfirmed and the step does not need it.
- **F6 (minor).** Step 6 should pigeonhole over pairs (newform, embedding) and note that `t_p` is
  integral.
- **F7 (minor, framing).** `p`-adic Hodge theory stays inside the citation of Serre's conjecture
  (Kisin's finite flat and potentially Barsotti–Tate methods). Route 1 removes only the direct
  uses of A009, A010 and Conrad. "No `p`-adic Hodge theory left in H" (route 2) should be
  qualified the same way.

## Suggestions

1. If route 1 is adopted, cite Serre's conjecture as KW I, KW II and Kisin 2009. Write a new audit
   record from the printed statement once those papers can be read, quoting it and stating whether
   it is the strong form.
2. Use the repaired steps 3-6 of `ser-ell.md` §4 in place of nt-h's text. Use the corrected
   trust-base table (`ser-ell.md` §5) for leaves-v2.
3. Pin the remaining locators against the printed sources: Raynaud §3.4 (inertia exponents),
   Serre 1987 §2 (recipe, peu ramifiée), Masser–Wüstholz 1995 §1.
4. A side question, not examined: whether Li's Fricke stability is still needed once the transfer
   targets `J₁(N)` directly.
