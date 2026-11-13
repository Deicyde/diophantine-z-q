# inner-twist results log

Base f90cf864 (wip/integrate-w38b). Targets: `G0ModField.InnerTwistCount` and
`G0ModField.UnramifiedConjugates` from `scratch/fibre-cover/FibreCover.lean`.

## InnerTwist.lean (imports ZInQKernel.HDecomp.QM.Structures, ZInQKernel.HDecomp.Textbook.SkolemNoether)
- `lake build` of QM.Pairs, Descent.B2Glue, Textbook.SkolemNoether, QM.Structures: success (1m54s). VERIFIED.
- File = scratch/aut-o-finite/AutOFinite.lean unchanged + header note + §IT.
- §IT: `InnerTwistCount` copied verbatim (docstring + body, namespace G0ModField); a script checked the
  748-character block of FibreCover.lean (docstring to end of def) is a substring of InnerTwist.lean. VERIFIED.
- `G0ModField.ad_comp_eq_comp_ad`: Ad v ∘ t = t ∘ Ad(t⁻¹ v).
- `G0ModField.innerTwistCount : InnerTwistCount` (W = image of the four reps of
  `Exact.autO_mod_inner_exact`, i.e. conjugation by 1, i, j, ij).
- `G0ModField.innerTwistCount_sharp`: every covering W has `4 ≤ W.card`.
- run (06:36, ~25 s): exit 0, 0 errors (linter warnings only, inherited §8); all 7 `#print axioms`
  [propext, Classical.choice, Quot.sound] (run_innertwist.txt). VERIFIED (compiled).
