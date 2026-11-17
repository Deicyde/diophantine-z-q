# tyz-genus — fleet summary (2026-11-16)

**Result.** TYZ Lemma 2.8 is proved in Lean with no new leaf (`ZInQ.Contrib.TYZGenusFold.tyzLemma28Sym :
H29Genus.TYZLemma28Sym`), so `hL29` follows from TYZ Theorem 2.1 alone
(`tyzLemma29PrintedNe3_of_thm21Pairs : TYZThm21Pairs → TYZLemma29PrintedNe3`; `#discharges`: hL29 discharged, still
assumes `[TYZThm21Pairs]`, standard axioms). `h11` cannot come from `TYZThm21Pairs` (integer sign choices make it
vacuous without Thm 1.1) nor from any instance of Thm 2.1 at `n > 1` (𝓛(1)² never isolated). Compiled alternatives:
* B: `h11 + hL29 → TYZThm21PairsC (complex sign choices) + TYZLcalOne (𝓛(1)² = 1)` — neutral; Thm 1.1 becomes glue.
* C: `h11 + hL29 → TYZThm21PairsC1` (Thm 2.1 including `n = 1`) — **−1**, but pending a reading of whether TYZ's
  Theorem 2.1 covers `n = 1` (source not on host). The `n = 1` instance is true and, with Cl(ℚ(i)) = 1, hp23's odd
  generator and t21-proof's certified L-value bounds, gives 𝓛(1)² = 1 in Lean.
Recommendation: fold C once a reader confirms n = 1 is in the print; otherwise B (or A = hL29 → TYZThm21Pairs only).

**Compiles (standard axioms, no sorry).** `ZInQKernel/Contrib/OneProof/TYZLemma28Sym.lean`, `TYZThm11Genus.lean`,
`TYZThm21PairsOne.lean`, helpers `TYZGenusFold/{Jacobi,Local,Ideles,Class,QI}.lean` (1212 lines): (−n/N I) = 1 and
Π_q χ_q([I]) = χ₄(N I); an explicit idele per ideal class with its τ̂-image and class; reduced norms on Brandt double
cosets; F = 0 where χ₀ = −1; Q(i) cyclotomic, PID, #μ = 4. Checks: `scratch/tyz-genus/Discharges.lean` (+output),
`FoldCheck.lean` (+output: variants A, B, C as `frozenTarget_thm21`, `_thm21C`, `_thm21One`), `fold-spec.json`,
`kinds-rows.tsv`, `log.md`. Report: `docs/research/tyz-genus.md`.

**Remains.** Reading TYZ Thm 2.1 (L554–559) / §2 setup for n = 1 (decides variant C). Nothing unproved in Lean.
