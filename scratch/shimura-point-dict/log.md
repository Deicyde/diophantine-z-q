# Shimura analytic points: results log

- VERIFIED: the fixed point predicate tests finite punctured limits of quotients of integral polynomials in the two generators. It quantifies over all complex points of the rational curve; the image point on the rational scheme need not be closed.
- VERIFIED: Mathlib's meromorphic order criterion gives a finite limit for nonnegative order. Negative order gives inverse limit zero. The finite germs in the image of a field form a valuation subring, including when the valuation is trivial.
- VERIFIED: `ShimuraPointDictGerms.lean` compiles with `lake env lean`. Axiom scan for all ten theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- VERIFIED (source): the vendored smooth-curve dimension module has `Scheme.valuationRing_stalk`; Mathlib has the proper and separated valuative criteria and the fraction-field instance for integral scheme stalks.
- VERIFIED: `ShimuraPointDictField.lean` compiles. The localization of the image of the integral polynomial ring gives a ring map from the model's function field to punctured germs. The comparison includes denominators vanishing at the parameter and the exceptional Weber branches.
- VERIFIED: `ShimuraPointDictGeometry.lean` compiles. The properness lift induces a surjective stalk map to the chosen valuation subring, and the section and stalk evaluations agree. The separatedness argument compares lifts from the same valuation subring.
- VERIFIED: the field and geometry scans cover 20 theorems and report only `propext`, `Classical.choice` and `Quot.sound`.
- VERIFIED: `ShimuraPointDict.lean` proves existence and uniqueness with the exact `AtTau` predicate. It supplies `HeckePin.X1TauPoints` and `HeckePin.ConstOnTauPoints`. The composite assembly now has only the two action laws as additional inputs.
- VERIFIED: `lake env lean scratch/shimura-point-dict/Integration.lean` checks the exact interfaces. Across the four contribution modules all 40 theorem scans report only `propext`, `Classical.choice` and `Quot.sound`; see `Axioms-output.txt`.
