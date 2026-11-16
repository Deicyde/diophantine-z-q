import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges

/-! Positive and negative controls for `#discharges` (task contrib-kit). Expected:
`t1` discharges `nvLocalInertia` and still assumes it; `t2` discharges nothing;
`t3` discharges `cartierSmooth` and is flagged for `sorry`. Its saved output, `DischargesTest-output.txt`, is
the worked example of `docs/one-proof/CONTRIBUTING.md`; rerun it after a fold. -/

theorem t1 (h : SGRDirect.NVLocalInertia) : SGRDirect.NVLocalInertia := h

theorem t2 : True := trivial

theorem t3 : _root_.AVGlue.CartierSmooth := sorry

#discharges
