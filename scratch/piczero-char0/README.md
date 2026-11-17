# scratch/piczero-char0

Report: docs/research/piczero-char0.md. Log: log.md.
- Taint.lean / FieldTaint.lean / Taint2.lean: closure analyses of frozenTarget (outputs *_out.txt).
- gen/build_char0.py + gen/char0_template.lean -> ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZero.lean.
- gen/gen.py (+ copylib.py, header.lean; reads taint2_out.txt) -> ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean.
- FoldCheck.lean: the manual fold (OpenAddedLeaves21, frozenTarget_pz); ClosureCheck.lean; Discharges.lean.
- fold-spec.md, kinds-rows.tsv, locators-rows.md: integration material.
- Iso.lean, Iso2.lean, RerouteCheck.lean: debugging scratch for the repeated-open timeout.
