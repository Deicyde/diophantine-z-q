# eps-splitting manual fold spec (hGZ is a frozenTarget binder: autofold.py does not apply)

Edits to `ZInQKernel/OneProof/Main.lean` (not made here; the integrator applies them). Against the current
`main` (binder type `ZInQ.GZAlg.GrossZagierAlgOptCd`):

1. Add `import ZInQKernel.Contrib.OneProof.GrossZagierSplit` (it imports `GrossZagierScheme`).
2. In `ZInQ.OneProof.frozenTarget`, retype the binder
   `(hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd)` -> `(hGZ : ZInQ.GZSplit.GrossZagierCurveCdSplit)`.
3. In the body, replace `ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ` by
   `ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSplit.grossZagierAlgOptCd_of_split hGZ)`.
4. kinds.tsv: replace the row `frozenTarget hGZ` by the row in `kinds-row.tsv`; locators.md: add the row in
   `locators-row.md`; regenerate OPEN.md.

If hgz-steps' fold (binder type `ZInQ.GZSch.GrossZagierCurveCd`) is applied first, step 3 instead replaces
`ZInQ.GZSch.grossZagierAlgOptCd_of_curve hGZ` by `ZInQ.GZSplit.grossZagierAlgOptCd_of_split hGZ` (or wraps it:
`ZInQ.GZSch.grossZagierAlgOptCd_of_curve (ZInQ.GZSplit.grossZagierCurveCd_of_split hGZ)`).

Check: `scratch/eps-splitting/FoldCheck.lean` is the result of 2-3 as a separate theorem
`ZInQ.EpsSplit.frozenTarget_split`; its `#print axioms` output is in `FoldCheck-output.txt`.
