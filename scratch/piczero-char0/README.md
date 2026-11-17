# scratch/piczero-char0

Report: docs/research/piczero-char0.md. Log: log.md.
- Taint.lean / FieldTaint.lean / Taint2.lean: closure analyses of frozenTarget (outputs *_out.txt).
- gen/build_char0.py + gen/char0_template.lean -> ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZero.lean.
- gen/gen.py (+ copylib.py, header.lean; reads taint2_out.txt) -> ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean.
- FoldCheck.lean: the manual fold (OpenAddedLeaves21, frozenTarget_pz); ClosureCheck.lean; Discharges.lean.
- fold-spec.md, kinds-rows.tsv, locators-rows.md: integration material.
- Iso.lean, Iso2.lean, RerouteCheck.lean: debugging scratch for the repeated-open timeout.

fold33-piczero (integration): `FoldCheck.lean`, `Iso2.lean` and `RerouteCheck.lean` redeclare `HDec.HSyn` bundles and
are renamed `.lean.txt`; the first-generation reroute `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean`
(built on leaf-fold33b 0e3c3125) is kept here as `PicZeroAbVarCharZeroReroute.lean.txt` and superseded by
`ZInQKernel/OneProof/H/PicZeroCharZeroCopy.lean`. `ClosureCheck.lean` and `Discharges.lean` import that module and
no longer compile as they stand (record of the first generation).
