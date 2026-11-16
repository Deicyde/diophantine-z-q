# H102 curve support — verified FLT source port

All six owned source edges compile on fixed Lean 4.35.0, with the exact original
`P2MW.S_AlgebraicCurve_<source>.solution` signatures. Each solution's complete
`#print axioms` output is exactly `[propext, Classical.choice, Quot.sound]`.
**This is not an H102 discharge or completed geometric bridge.**

The five assigned giants plus transferred `tateChainRule` are factored into
23 proof parts and six original-path import facades. One additional small proved
linear-conjugation helper supports an explicit 4.35 cancellation step. All 30
Lean files are at most 136,967 bytes. No existing repository module, pin, target,
configuration, or other author's source is changed by this contribution.

* `VERIFICATION.md`: checks run, compatibility edits, provenance, and limitations.
* `CURVE_SOURCE_MANIFEST.json`: immutable source hashes, exact source-line ranges,
  helper mappings, current file hashes, and native checks.
* `SOURCE_AUDIT.json`: unchanged original signatures and prohibited-code scan.
* `Compile/verified/CurveProofCheck.log`: all six full types and full axiom outputs.
* `Compile/verified/`: successful compiler logs for every part/facade/helper.
* `Compile/ATTEMPTS.md` and `Compile/attempt00/`: labelled historical failures.
* `PREFLIGHT.md` and `Preflight/`: earlier small prerequisite availability checks.

Original FLT revision: `6e837e75355538c7f80bab5b956861e86c4eacc2` (Lean 4.33.1).
Full upstream Apache-2.0 LICENSE, NOTICE, and attribution accompany this directory.
Each owned source file carries its modification notice. The final review base is
`e22df37cdef936f5b0f29ec09501854bea6c7316`, with unchanged Lean/Mathlib pins and H102
target relative to the initial good `0e70c94e` / restored `2dc949d6` source base.

The RR theorem's original residue-theorem input is retained; the separately
compiled global residue theorem supplies it honestly. No result is replaced by
an axiom, assumed target, weaker statement, or custom runtime checker. The primary
author owns the final H102 bridges, exact `#discharges`, review, and integration.
