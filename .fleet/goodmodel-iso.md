# goodmodel-iso (fleet summary)

**Verdict: target met.** group-law-dvr's glue `NeronGoodModelIso` is proved. No purity is used, and no `sorry`; the
axioms are the standard three (VERIFIED). The input is the DVR case of the leaf that fold F2 already carries:
`ZInQ.Contrib.GoodModelIso.neronGoodModelIso_of_dvr : NeronSchemeExtensionDVR → NeronGoodModelIso`, hence
`mumfordGroupLawDVR_of_dedekind : NeronSchemeExtensionDedekind → MumfordGroupLawDVR`.
- The suggested step "F is a Néron model (BLR 1.2/8)" is circular: the tree's proof needs a group law on F.
- The proof works in the target instead:
  - the FLT extension of ψ_K⁻¹ to an open V that contains every codimension ≤ 1 point;
  - injectivity of ψ on the special fibre, by rigidity (`MulRigidity`) and translation by field-valued points;
  - Hartogs into affine opens (vendored FLT);
  - the general N reduced to the Néron model N'.

**Fold G (manual, VERIFIED in an olean overlay).** G is group-law-dvr's F2 without the glue field, plus the removal of
the textbook field `neronSchemeExtensionExists`.
- `mumfordGroupLawConn` and `neronSchemeExtensionExists` are replaced by the one printed leaf
  `neronSchemeExtensionDedekind` (BLR 1.4 Thm 3): net −1, no new glue.
- 42/42 downstream modules compile, and `frozenTarget` has standard axioms.
- `#discharges` on the folded tree: 44 open hypotheses, against 45 before. `MumfordGroupLawConn` is out of the closure.
- Files: scratch/goodmodel-iso/fold/ (make_patch.py, G.patch, compile_overlay.sh, FoldCheck.lean, foldcheck-G.txt,
  compile-G.txt, autofold-G.json marked manual).

**What compiles.**
- The new file `ZInQKernel/Contrib/OneProof/NeronGoodModelIso.lean` (about 620 lines).
  `lake build ZInQKernel.Contrib.OneProof.NeronGoodModelIso` succeeds.
- `#discharges` on the unfolded tree (scratch/goodmodel-iso/discharges.txt):
  `neronSchemeExtensionExists` is discharged by `neronSchemeExtensionExists_of_dedekind`.

**What remains.**
- An integration build of G, the hash comparison, and the kinds.tsv/OPEN.md regeneration.
- A locators.md row for BLR 1.4 Thm 3, whose locator is UNVERIFIED.
- Apply G rather than neron-ext's count-neutral fold of the same textbook field.

Report: docs/research/goodmodel-iso.md. Log: scratch/goodmodel-iso/log.md.
