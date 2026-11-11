# rv-redei: report

**Verdict: no blocker.** The full review is in `docs/research/rv-redei.md`.

## What was checked
1. **Faithfulness.**
   - `QNeg n = QuadraticAlgebra ℚ (−n) 0` is `ℚ(√−n)` with Mathlib's field structure.
   - `𝓞` is the full ring of integers.
   - `gCl n = Nat.card (Cl²)` is TYZ's `g(n) = #2Cl(ℚ(√−n))`.
   - `gBit` is tyz-5b Proposition 2.3 term for term.
   - `T5bCl` is the `(7, 3)` genus sum of nt-tyz Proposition N.
   - `RedeiFormula` states what its docstring says. The hypothesis `B.Nonempty` is needed: at
     `B = ∅`, `gBit = 0` but `g(1) = 1`.

   **PARI:** on 30 pairs `(d, B)` (1 to 5 primes in `B`, classes 7, 3, 1 mod 8), `gBit` transcribed
   from the Lean definitions equals the parity of `#Cl²` in 30/30 cases, with both parities
   occurring (`scratch/rv-redei/gbit_check.py`, `.out`).
2. **Vacuity and junk values.** `redeiFormula` is a closed statement about `gCl` and `gBit` only, and
   no internal junk value (`chi`, `ramIdeal`, `ambigClass`, `ramSet`, `redeiEntry`) appears in it.
   Every junk branch is guarded by the hypotheses where it is used. A scratch Lean file (deleted)
   derived `Odd (gCl 7)`, `Odd (gCl 19)` and `Even (gCl 17)` from `redeiFormula`, all true, so the
   hypotheses can be met and the conclusion carries information. `OddGClStatement` with `1 < n` is
   correct at the edge cases `n = 3, 5, 17`.
3. **Main-theorem variants.** Compared with the merge parent, the `…_certifiedRankTYZCl` and
   `…_certifiedRankTYZClRk` terms differ only in that `hR` is removed and `redeiFormula` is
   supplied. `KERNEL_PLAN.md` and the trust statements in Statements.lean, CertifiedRank.lean,
   Covering.lean and TYZ.lean describe the hypotheses accurately, apart from N1 and N2 below.
4. **Build.** `lake build ZInQKernel` succeeded (9918 jobs). `scripts/print_axioms.lean`: all 50
   entries show only `[propext, Classical.choice, Quot.sound]`.

## Non-blocking findings (docstrings only; I edited no Lean, per the task)
- **N1.** `ZInQKernel/RouteK/Rank5b/Sec3/TYZ.lean:107–108` says "for every set `B` … `gBit d B =
  #2Cl mod 2`". This is false for `B = ∅`. It should say "every nonempty set"; the `d_B ≢ 5`
  restriction is unnecessary, because `gCl_dProd_eq_gBit` covers every nonempty `B`.
- **N2.** `TYZ.lean:92–93` says "none of them formalized here", which contradicts its own bullet
  saying Rédei's formula is proved in Lean.
- **Cosmetic.**
  - The `CertifiedRankTYZCl` docstring could cite the unconditional `Redei.certifiedRankTYZ_iff'`.
  - `KERNEL_PLAN` says "eight modules", but there are nine files (counting `Entry.lean`).
- **Stale page outside the Lean tree.** `blueprint/roadmap/rank-5b/certified-rank-5b.md:16–34`
  still says "none of which is formalized". It also states TYZ's conclusion as "`2^{−ρ}𝓛(n)` odd"
  instead of Proposition N's "`𝓛(n) ≠ 0`".

## Suggestions
Fix N1 and N2 in TYZ.lean the next time someone edits trust statements, and refresh the blueprint
page.
