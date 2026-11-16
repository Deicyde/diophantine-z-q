# jp-compile: fleet note

**Verdict.** Draft fork PR #38 (a9bc2e35) proves `hJP : H29Split.JonesPallX2Y2Z16` exactly, with no new leaves.
VERIFIED on Lean 4.35.0 / Mathlib v4.35.0 after merging origin/main 0caafe66:

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.JonesPall`
  succeeds with no technical fix. This task changed no file under ZInQKernel/.
* `#discharges`: `DISCHARGES [hJP] by ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof`, still assumes `[]`,
  axioms `[propext, Classical.choice, Quot.sound]`. No native_decide anywhere (no `Lean.ofReduceBool`).
* The binder `hJP` of `frozenTarget` has a type syntactically equal to the theorem's (MetaM check), and `rfl`
  holds.
* `scratch/jp-compile/FoldCheck.lean` (main's Main body with `hJP` dropped and the proof passed) compiles with the
  standard axioms. Result: one fewer top hypothesis (56 to 55).
* The PR only adds files under Contrib/OneProof/ and has no build-time code. Its LegendreThreeSquares/ files are
  byte-identical to PR #36 and leaf-fold32b.

**Proof idea.** Two squares when no prime factor of n is 3 mod 4. Otherwise: Legendre (the atlas-lean port), then
a quaternion conjugation `q v q̄ / p` with `N(q) = p ≡ 3 (mod 4)` that fixes the mod-4 pattern.

**Remains.**
* autofold cannot fold a frozenTarget argument (the dry run says "not a field"), so the integrator folds by hand
  as in FoldCheck.lean.
* kinds.tsv: drop the `hJP` row (LEAF goes down by one, GLUE unchanged).
* The fold over leaf-fold32b's Main (after the `hL3s` fold) is the same substitution and is UNCHECKED.

Report: docs/research/jp-compile.md.
