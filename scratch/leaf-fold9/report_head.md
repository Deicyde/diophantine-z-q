# leaf-fold9: `r1rec` and `r5` proved from `r1r2`, cloud PR #11 and modular-split's `r15` folded into the single proof; 61 fields, strict GLUE 24 (was 27 of 66)

Task leaf-fold9, 2026-11-14. Base 5da857b0 (wip/w59: fork main e9240be8 (w58) with leaf-fold8 inside OneProof,
mcr-quot, coarse-factor and cloud PR #11). Merged: `origin/wip/modular-split` (fold (4)). New Lean:
- `ZInQKernel/OneProof/H/TailZ5.lean` (the proofs) and `TailZ6.lean` (modular-split's `R15.lean` and the bundles);
- the switch of `ZInQKernel/OneProof/Main.lean`.

Each new module is under 150 KB. Checks and tools are in `scratch/leaf-fold9/`; the results log is `log.md`. No
existing OneProof module was edited. No other file under `ZInQKernel/`, `blueprint/`, or another task's files was
edited either. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator is the source report's. It is UNVERIFIED unless the audit `locators.md` read it.
