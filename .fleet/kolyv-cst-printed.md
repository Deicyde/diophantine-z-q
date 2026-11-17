# kolyv-cst-printed (fleet note)

**Result.** Kolyvagin Theorem 1 and Cai–Shu–Tian Theorem 1.1 are stated in printed form as cited
leaves, with no proofs and no Gross–Zagier/TYZ argument. Base: main `d435851d` + `origin/wip/pc-from-rc`
(clean merge). Report: `docs/research/kolyv-cst-printed.md`.

**Compiles** (`lake env lean` and `lake build`, no errors, warnings or `sorry`; all 33 new
declarations use only `propext`, `Classical.choice`, `Quot.sound`):
* `ZInQKernel/Contrib/OneProof/KolyvCST/Kolyvagin.lean`: `KolyvaginThm1Printed` (r ≤ 1, as the
  manuscript cites it at tex L1093), the bridge to pc-s12's `KolyvaginThm1` (r = 1), Lemma 5.5 in
  full (`ForwardRank`, `ForwardCorank`) from BCDT + Kolyvagin + `MordellWeil` + `KummerCorank`
  (textbook GLUE), and `kolyvaginRankOne_of_forwardRank` for pc-from-rc's `KolyvaginRankOne`. The
  r = 0 case is needed by the proof of Theorem 5.3 (tex L2386, L7626, L7780, L8264).
* `ZInQKernel/Contrib/OneProof/KolyvCST/CaiShuTian.lean`: `CSTThm11Split`, a special case of
  Theorem 1.1 (non-CM `E`, all primes of `N` split, `disc K ≠ −3, −4`, `gcd(c, N) = 1`, primitive
  `χ`, constant replaced by `∃ C > 0`). This is exactly the domain of both manuscript uses
  (tex L2428–2432, L8268–8272). It is stated over Mathlib's `℘`/L-factors/cusp forms and Tau
  Ceti's ring class field, Artin map, Néron–Tate pairing and Eichler integral. Written fresh and
  flagged: `newformLevel`, `phiAn`, `twistedLFunction`, `heightK`. Also two usage lemmas
  (nonvanishing ⇔ nonzero height; ratio of two instances).

**Not done / remains.**
* No print was read (no network). Every clause is UNVERIFIED (pending reading), so both leaves
  count GLUE. The report's §8 lists the pages to check: Kolyvagin MPI/90-69 pp. 3–5, and CST
  ANT 8 (2014) pp. 2524–2525.
* Stop rule: `X₀(N)/ℚ`, algebraic Heegner points, `deg φ` and Rankin–Selberg `L(f × θ_χ)` are absent
  from Mathlib and Tau Ceti. The CST statement uses the analytic model and an Euler product over
  `K`. These translations are provenance (c), argued in the report §2.2, not LEAF.
* No manuscript error found. Gaps recorded: Kolyvagin's "modular" is Weil-modular, not the
  L-series `IsModular`, so the leaf over `IsModular` is a consequence of BCDT + Kolyvagin together.
  The CST bibitem has no pages or locator. At tex L8269, the vanishing `L(E^{(D_w)}, 1) = 0`
  (root number −1) is implicit. The pc-s12 docstrings cite tex L1099/L1100 where this base has
  L1092/L1093.
