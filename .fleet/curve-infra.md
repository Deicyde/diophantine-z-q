# curve-infra (2026-11-13)

**Verdict.** image-plane's proof of `MobiusGlue` from T5 needs none of (AD), (IC), (L0): it proves
(IC) and (AD) itself, and its C2K route avoids (L0) (read in docs/research/image-plane.md §1, §7).
So, per the task, I proved (AD) in general: **for an integral scheme `X` locally of finite type over a
field `K`, `dim X = trdeg_K K(X)`** — Lean, Mathlib only, no hypotheses, standard axioms.

**What compiles** (`scratch/curve-infra/CurveInfraAll.lean`, 0 errors, all 8 theorems with axioms
[propext, Classical.choice, Quot.sound]; VERIFIED, run_CurveInfraAll.txt):
- `DimEqTrdeg` (schemes), `DimEqTrdegAlg` (f.g. domains: dim R = trdeg Frac R) — via Mathlib's
  Noether normalization, going up, trdeg tower law, and the affine-open cover;
- `AlgDepOfTrdegOne`, `SmoothTrdeg` (smooth integral of rel. dim n ⇒ trdeg K(X) = n, with
  infra-smooth-dim), `CurveFnFieldAlgDep` (any two rational functions on a smooth curve are
  algebraically dependent);
- `DimEqTrdegOver`, `SmoothTrdegOver`, `CurveAlgOverTranscendental` over the kernel's own
  `ZInQ.LeafPush2.ffAlgebra` (R18.lean), so they apply directly to `HasSexticModel`/R18 contexts.
- `Dim.lean` (Mathlib-only core) also compiles alone, 0 warnings. Copied code verified verbatim
  (`py/verbatim.py`, ALL OK).

**What remains.** Nothing in the image-plane chain. (L0) `FiniteGlobalSections` (EGA III 3.2.1) is
no longer used by any proof and was not attempted. Integration: `Dim.lean` can become a kernel module as is.
Report: docs/research/curve-infra.md; log: scratch/curve-infra/log.md.
