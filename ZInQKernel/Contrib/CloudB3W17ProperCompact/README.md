# Integral proper compactness

Base: `e22df37cdef936f5b0f29ec09501854bea6c7316`.
Lean `4.35.0`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

`W17ProperCompact.compactSpace_complexPoint_of_isIntegral_isProper` proves that the
native analytic complex points of every integral proper complex scheme are compact.
`W17ProperCompact.compactSpace_complexPoint_abVar` applies it to every actual
`PkgI3.AbVar ℂ`, with no projectivity or compactness premise on the target.

The proof uses a surjective projective Chow cover. The cover is projective through
the actual graded-polynomial/terminal-pullback isomorphism in `ProjBridge.lean`, not
through a named-shape identification. `PointLift.lean` lifts field-valued points
through a surjective locally finite type map using a closed point of its fibre.
`NativeCompact.lean` then takes a continuous surjective image of the compact
projective point space.

Dependencies, used without source changes:
- Existing W02 vendor of `anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2`.
- Hodge core commit `e222d7ba1999d47ab0618cc0d812bb0b6f8b7229`.
- Hodge projective-compactness companion `9fbc627ae28ffa756cdf33f2c8995eddce06601a`.
- Both Hodge slices come from `Paul-Lez/HodgeConjecture@2ead713179628a3c738197d5996f51c8a9c886ac`.

The imported source trees retain their notices and licenses. `LICENSE` here is
Apache 2.0. `BUILD_REPORT.md` records the checks; `CHECK_OUTPUT.txt` contains the
full theorem-type and axiom output. All thirteen supplier constants and both
compactness donors use only `propext`, `Classical.choice`, and `Quot.sound`.

This is a restricted compactness supplier. General nonreduced/component cases and
the separate dictionary to `UnifPrinted.CPt` / `A.Pt ℂ` are not claimed here.
Neither H103 nor `ProperCompactAn` is claimed discharged by these files alone.
