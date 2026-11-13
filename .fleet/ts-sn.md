# ts-sn (fleet summary)

**Verdict:** both targets are now theorems with no hypotheses, and neither statement was changed.
Compiled; standard axioms only.
- `PropTSGlue.snSpecialize : SNSpecialize` is **proved here** (new).
- `PropTSGlue.verticalResidueSeparable : VerticalResidueSeparable` was already proved by
  prop-ts-glue (`verticalResidueSeparable_of_degree verticalResidueDegree`); here it is only
  restated as a named theorem.

Consequences:
- `PropTSGlue.specNonMeeting : SpecNonMeeting` holds with no hypotheses.
- Proposition TS now needs only 12 open glue Props: the seven Kummer pieces and the five Hecke
  pieces (`propTSAll_final'`). It still rests on T2, `R1R2fp` and `MobiusGlue`. The count was 13
  before.

**Proof idea:**
- Let `A = ψ(S)`, where `ψ : S = ℤ[X]_m-closure → ℚ(φ(B/𝔓))` is reduction modulo `𝔓`. In `ℤ[X]`,
  `g ∈ m ⟺ p ∣ d^k g(s₀)`.
- Since `R → S` is étale, `R → A_q` is formally unramified, so `max(A_q) = m·A_q = (p)`
  (Mathlib's `FormallyUnramified.map_maximalIdeal`).
- So each `A_q` is a DVR, `A` is normal, and `A` is `𝓞_L` localized at the integers prime to
  `p`. Hence `e(Q/p) = 1`. This last part is the abstract criterion `unramifiedAt_of_subring`.

**What compiles (VERIFIED):** `lake env lean scratch/ts-sn/TSSN.lean` gives:
- 0 errors and no `sorry`;
- 69 `#print axioms` lines, all reading `[propext, Classical.choice, Quot.sound]`;
- `check_prefix.py` prints `PREFIX IDENTICAL`: the file starts with prop-ts-glue's
  `PropTSGlue.lean` verbatim.

To compile it, first run `lake build ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue`.

**What remains:** nothing for this task. Under Proposition TS, the Kummer and Hecke pieces of
prop-ts-glue are still open. No new leaf was introduced. No human has reviewed this work.

Report: docs/research/ts-sn.md. Log: scratch/ts-sn/log.md.
