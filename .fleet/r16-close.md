# r16-close (fleet summary)

**Verdict.** `r16CoreY` is discharged, but the GLUE count is unchanged: 11/18 on 29 → 15/18 on 33 (LEAF/GLUE),
not the hoped-for −1 GLUE. The reason is a statement check: Diamond–Shurman Thm 9.5.4 prints that
`ρ_{f,λ}(Frob_𝔭)` *satisfies* `x² − a_p x + χ(p)p = 0`. It does not say "characteristic polynomial" (Thm 9.5.4,
2016 corrected fourth printing, pp. 401–402; human read, issue #14 comment 7121091136). So aftate-fix2's
`AfTateDSLambda` is stronger than its print. The fold uses aftate-fix2's fallback pair instead:
- `AfTateDSLambdaSat` (DS Lemma 9.5.3 + Thm 9.5.4 as printed): LEAF.
- `AfDetLambda` (`det ρ_{f,λ}(Frob_p) = χ(p)p`): GLUE, no print found. Candidates Shimura 1971 Thm 7.14 and Ribet
  1977 are unread.

`AfTateLam.r16CoreY_of_sat_det : HeckeJ1DS → AfShimura → AfTateDSLambdaSat → AfDetLambda → IgusaGL2DS →
MumfordTorsionAlgClosed → R16CoreY`, in the new file `ZInQKernel/Contrib/OneProof/R16CoreYSatDet.lean`, standard
axioms.

**Fields on main.** `mumfordTorsionAlgClosed` is an open textbook LEAF on main. PR #54 proves it (fold34-pr is
folding it), so after that fold substitute `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`.
`IgusaGL2DS` is not on main and enters as a new leaf.

**Compiles (VERIFIED).**
- aftate-fix2's chain builds unchanged on main c0f3d085c (14233 jobs).
- `#discharges`: `DISCHARGES [OpenResearchLeaves31.r16CoreY] by AfTateLam.r16CoreY_of_sat_det`, standard axioms.
- Verbatim target copy, with an `Iff.rfl` check.
- Fold dry run `scratch/r16-close/autofold.json`: `sixContactMin_of_open49` compiles with standard axioms.

**Leaf ratings.** DS Lemma 9.5.3, Thm 9.5.4 and Thm 9.6.5 are covered by human reads (issue #14 comments
7000317188, 7121091136); the other DS locators below were AI-read only and are not claimed as read.
- `heckeJ1DS` (DS §6.3, Prop 5.2.1, §7.9): printed form.
- `afShimura` (Shimura 1973 Thm 1; DS Def 6.6.3): printed form.
- `afTateDSLambdaSat`: printed form.
- `igusaGL2DS` (DS Thm 7.6.3, (7.12)): printed form.
- `afDetLambda`: not printed form (GLUE).
- No leaf was proved outright: the tree has no infrastructure for Hecke correspondences on modular Jacobians.

**Remains.** A printed source for the determinant (or the per-λ trace) of `ρ_{f,λ}` on `A_f`. Finding one turns
`afDetLambda` into a LEAF, and then the count drops by one GLUE. Locators.md rows are proposed in the report, not
added. Report: docs/research/r16-close.md.
