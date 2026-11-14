# leaf-fold9: `r1rec`, `r5` proved from `r1r2`; cloud PR #11, modular-split's `r15` and reduct-split's `r7b`, `r8` folded into the single proof; 63 fields, strict GLUE 22 (was 27 of 66)

Task leaf-fold9, 2026-11-14. Base 5da857b0 (wip/w59: fork main e9240be8 (w58) with leaf-fold8 inside OneProof,
mcr-quot, coarse-factor and cloud PR #11). Merged (fold (4)): `origin/wip/modular-split`, `origin/wip/reduct-split`. New Lean:
- `ZInQKernel/OneProof/H/TailZ5.lean` (this task's proofs), `TailZ6.lean` (modular-split's `R15.lean`),
  `TailZ7.lean` (reduct-split's `Reduction.lean`) and `TailZ8.lean` (the bundles);
- the switch of `ZInQKernel/OneProof/Main.lean`.

Each new module is under 150 KB. Checks and tools are in `scratch/leaf-fold9/`; the results log is `log.md`. No
existing OneProof module was edited. No other file under `ZInQKernel/`, `blueprint/`, or another task's files was
edited either. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator is the source report's. It is UNVERIFIED unless the audit `locators.md` read it.
