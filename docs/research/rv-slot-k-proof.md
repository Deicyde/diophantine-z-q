# Referee report on the proof of the descent lemma in `slot-k.md` §2

This report checks the proof of the descent lemma DL given in `docs/research/slot-k.md` §2: the
configurations and the use of Proposition 0 (§2.1), the two gluing lemmas (§2.2), the base
configuration (§2.3), the slots (§2.4), the proof of DL (§2.5) and the count (§2.6). It also checks
that DL, as proved, is the statement that Route K needs. Every step was redone by hand. The
computations below are independent implementations: none imports the code of `scratch/slot-k/`
or `scratch/descent-alt/`.

Each examined step is marked **CORRECT** (checked here), **GAP** (missing or wrong) or
**UNCHECKED**.

## Verdict

**DL is proved as written.** I found no mathematical gap in §2. Every cancellation and every sign
in Lemmas 1–3 and in steps 0–6 of the theorem is right, the residue conditions on the auxiliary
primes are always simultaneously satisfiable, and the conclusion is exactly what the `x + ℓ`
version of the pole polynomial needs, once a certificate of Selmer type is turned into a rational
point by the deep input (Kriz's rank-one 2-converse with the corank lemma).

The findings are all minor. None affects the validity of DL:

| # | Severity | Where | Finding |
| --- | --- | --- | --- |
| 1 | minor (inaccurate commentary) | §2.4, §2.5 "What each slot does" | The condition `[q₀/ℓ] = 0` for `ℓ ∈ T` is never used. Symbols between `q₀` and `T` lie inside the glued set of step 5 and drop out of Lemma 2. The note says they are "dictated by the transfer to the second curve"; they are free. |
| 2 | minor (overstatement) | introduction, §2.6 | "Within one of the lower bound of Proposition B" holds only when `ω(β) = k + 1`. In general the construction uses `ω(β)` auxiliary primes for the first curve, against the lower bound `k ≤ ω(β) − 1`. |
| 3 | minor (wording) | §2.1, "Odd places and the real place" | The sentence "classes are automatically unramified outside `2d∞`, since they are supported on `−1, 2` and the primes of `d`" states the easy direction. The proof needs both directions: Selmer classes are unramified outside `2d∞` (Silverman X.1.4), so they are supported on `−1, 2` and the primes of `d`; conversely such classes satisfy the local conditions at every `p ∤ 2d` automatically. Both are standard. |
| 4 | minor (citation) | §1.2, §4.1 | Kriz's Theorem 10.17(2) sits under header hypotheses belonging to its part (1); pc-audit RK1 recommends citing Theorem 10.13 directly. Kriz's standing assumption `f₀ ≥ 4` should be checked explicitly; here it is immediate, since `f₀ = |n|` or `|n|θ` and `|n| ≥ 7·3 = 21`. |
| 5 | minor (presentation) | §1.2 | The torsion certificate is phrased loosely ("`(β, 0)` or `(−β, 0)` lies on `C_d` up to the identification"). The construction never produces a torsion certificate, so this is immaterial to DL. |

No repair is needed for the proof. Findings 1–5 are editorial. The repairs section lists the
suggested rewordings.
