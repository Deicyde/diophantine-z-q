# rv-barrier log

Task: adversarial review of Theorem G (docs/research/el-gadget.md §1, column form, E1/E2)
and Lemma G (docs/research/el-special.md §4, C3/C5).

## Step 1. Read both notes (done)
Objects under review:
- TG-a dichotomy, TG-b transfer, TG-c fibres with F_m-points, Theorem G, column form, Stein remark,
  global-soundness paragraph (el-gadget §1); column property (§2).
- Lemma G, Cor 1-4, scope paragraph (el-special §4); C3 (route M), C5 (Cor 2).

## Step 2. The soundness the barriers assume (inspection of Lean, no Lean run)
- `PoleSoluble B` (ZInQKernel/Hypotheses/Pole.lean:52): rational zero of `polePoly`; witnesses
  bits b (b²=b), e, z, r1, r2, w with r1² = A(A²-e²), r2² = A(A²z⁴-e²H²), w·eHz = 1, A = mB,
  H = A(A-B²), m = product of (1-2b0)...(1+12b5) (a unit at p ∤ 2730).
- Fibre over B: conic in (e,r1), and over each e a genus-1 quartic in (z,r2). Not RC: consistent with
  Theorem G (no contradiction from the existing gadget).
- Soundness proof `poleSystem_no_negative_odd_valuation` (Multiplication/Certificate/Parity.lean:93)
  uses only padicValRat identities (min rule, parity of 2v(y)); the same argument works verbatim for
  Q_p-witnesses. So the current soundness is LUS with p0 = 13 (p ∤ 2730). VERIFIED (inspection).
- `pole_step` (Assembly/Local/TestDivisibility.lean:225) consumes only `¬(v_p(B)<0 ∧ odd)` at p > 13.
