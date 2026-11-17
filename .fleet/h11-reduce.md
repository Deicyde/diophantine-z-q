# h11-reduce (2026-11-16)

**Verdict: h11 removed, net −1 hypothesis.** `TYZThm11Integral` (TYZ Thm 1.1, integrality of 𝓛 on classes 1, 3)
is proved in `ZInQKernel/Contrib/OneProof/TYZThm11Integral.lean` (`tyzThm11Integral_of_leaves`). It uses the open
leaves `LegendreThreeSquares`, `JonesPallX2Y2Z16` and `TYZTestVectorExists`, plus two printed leaves:
* `TYZLemma29PrintedNe3R`: TYZ Lemma 2.9 (n ≠ 3) for **real** sign choices of 𝓛. This is the print, and it implies
  the open `hL29`. The open integer-ℓ form presupposes Thm 1.1 (it is vacuous otherwise), so it cannot give h11.
* `TunnellOddL1`: Tunnell 1983 (Invent. Math. 72), L(C_n,1) = β(A−2B)²/(16√n) for odd squarefree n. Theorem number
  UNVERIFIED; checked numerically on 30 n with PARI. Only n = 1, 3 are used: they give 𝓛(1)² = 𝓛(3)² = 1, which
  closes TYZ's two gaps (the asserted 𝓛(1) = 1 at L1082, and the false Lemma 2.9 at n = 3).

The same leaves give h29 without `TYZThm21At31` (`tyzLemma29Mod2_of_tunnellR`). frozenTarget's TYZ arguments go
from 9 to 8: h11, hL29 and hT21 are removed; hL29R and hTun are added, all LEAF in both the strict and strictest
columns.

**Compiles (VERIFIED):** the new file has no sorry, no warnings and only the standard axioms. `lake build
+Main +Discharges +TYZThm11Integral` passes. `scratch/h11-reduce/MainEdit.lean` (`h11reduce_frozenTarget`, the
manual fold) compiles with the standard axioms. `#discharges` reports `[h11]` and `[hL29]` discharged
(`DischargesH11-output.txt`).

**Remains:** the fold is by hand, because these are frozenTarget arguments (`autofold.json` documents it, with
`manual_fold`; kinds rows are in `kinds-rows.tsv`). Someone needs to read Tunnell 1983 for the theorem number and
which display is printed. A `locators.md` row is needed. Report: `docs/research/h11-reduce.md`.
