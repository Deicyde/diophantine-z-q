# r16-det (fleet summary)

**Verdict: −1 GLUE.** The printed characteristic equation (so also the determinant) of the Section 9.5
realization `ρ_{f,λ}` on `A_f` is in **Diamond–Shurman Thm 9.6.5 at k = 2** (2016 corrected
fourth printing p. 404; VERIFIED by a human read, issue #14 comments 7000317188, 7121091136). The theorem prints "the characteristic equation" of
`ρ_{f,λ}(Frob_p)`, `x² − a_p x + χ(p)p^{k−1}`. In the paragraph right after it, DS say that Section 9.5
constructed `ρ_{f,λ}` for k = 2 but did not prove irreducibility or that the equation is the characteristic
equation. So at k = 2, 9.6.5 is a statement about the 9.5 representation `e_λ V_ℓ(A_f)`.

**Lean.** New file `ZInQKernel/Contrib/OneProof/R16CoreYDS965.lean`:
- `AfTateLam.AfCharpolyDS965`: the new leaf. It is aftate-fix2's `AfTateDSLambda` verbatim (`Iff.rfl`),
  re-sourced to DS 9.6.5.
- `afDetLambda_of_ds965`: r16-close's GLUE `AfDetLambda` is a consequence.
- `r16CoreY_of_ds965 : HeckeJ1DS → AfShimura → AfCharpolyDS965 → IgusaGL2DS → MumfordTorsionAlgClosed →
  R16CoreY`, with standard axioms.

**Compiles (VERIFIED).**
- The contribution builds.
- `#discharges` shows `r16CoreY` discharged by `r16CoreY_of_ds965`.
- The verbatim target copy checks with `Iff.rfl`.
- The fold dry run `scratch/r16-det/autofold.json` gives `11/18 on 29 -> 15/17 on 32`, and
  `sixContactMin_of_open49` has standard axioms.

**Leaf rating.** `afCharpolyDS965` is printed form. Reading risk: the k = 2 identification is in DS's text
after the theorem, and the theorem itself is phrased existentially. Shimura 1971 Thm 7.14 and Ribet 1977 are
not on this host and remain unread, as a possible second locator. The other leaves are as rated by r16-close.

**Also.** The host path in r16-close's report and log is removed.

**Remains.** A human reading of DS Thm 9.6.5 at k = 2 (since posted: issue #14 comment 7121091136). The spec keeps `{t}.mumfordTorsionAlgClosed`; substitute PR #54's
proof after fold34-pr. Report: docs/research/r16-det.md.
