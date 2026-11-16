# Tian–Yuan–Zhang Theorem 3.3: printed-input reduction

This contribution reuses the existing reduction of `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` at project revision `d489fc13f1eadba5ca95d61b8f455cd2b0e7c402`.

The exact target is derived from the already-open complex-multiplication input and one printed Tian–Yuan–Zhang Theorem 3.3 input. This is a reduction, not an unconditional Gross–Zagier proof. The original target and all existing modules and dependency pins remain unchanged.

The entry point is `CloudB3SC7H33.h33_proof` in `ZInQKernel/Contrib/OneProof/TYZThm33.lean`, with explicit inputs `T5Glue.ShimuraMainCM` and `H33Dict.TYZThm33Printed`. The complete existing reduction is reused; no new Gross–Zagier proof is supplied. [Source reuse](SOURCE_REUSE.md) records the immutable original and comment-only changes; [printed-source comparison](SOURCE_AUDIT.md) gives the journal locator, weakenings and interpretation boundaries. AI reading does not clear human-reading flags.

Verified on Lean 4.35.0 and unchanged Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:

- The module and current Main/Discharges prerequisites build successfully. The source hash is `ed2c571d303bf4ea2ba5af72f9acda57c5d93183c582edeedc3cbf7e3894a258`.
- Exact two-premise, named-target and fully expanded original-type assignments compile with `autoImplicit false`. An initial private checker's missing namespace qualification was corrected; the proof source was unchanged and the failed log is retained.
- All 45 explicit named declarations were queried for axioms. Each uses only a subset of the standard three; `h33_proof` uses exactly `[propext, Classical.choice, Quot.sound]`.
- The prescribed three-import `#discharges` check reports `DISCHARGES [h33] by CloudB3SC7H33.h33_proof`, still assuming `[T5Glue.ShimuraMainCM, ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed]`, with the standard three axioms. Full output is in the pull request.

Independent source, mathematical and recorded-evidence review passed for this conditional reduction. It does not certify a new unconditional Gross–Zagier proof, a Lean scheme-equivalence dictionary, human source acceptance or an independent imported-library raw replay. The claim-only version remains in Git history. The integrator should retain the new printed leaf's unread/human-reading flag and apply the manual top-level-argument fold; no fold or target edit is performed here.

AI-assisted contribution operated by Jack McCarthy. Private evidence bundle available to the maintainer.
