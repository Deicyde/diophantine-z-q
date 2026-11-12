# glue-a6-alg (final)

**Result: A6 (Lemma PR(ii), Raynaud route) now follows in Lean from the three I2 leaves alone**
(`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`). Both open glue items that
rv-a6-route left are proved. Everything below is VERIFIED: it compiles with `lake env lean`, has
no `sorry`, and its axioms are only [propext, Classical.choice, Quot.sound].

- `GlueA6Alg.quatUnipotentTrivial : QuatUnipotentTrivial` (scratch/glue-a6-alg/Quat.lean, and in A6.lean).
  - Core theorem `GlueA6Alg.core`, over V = (ZMod 3^{2k})^4:
    - a vector x with Jx ≢ 0 mod 3 exists;
    - x, Ix, Jx, IJx are independent over F_3, because a²−2b² is anisotropic mod 3, so no |T/JT| count is needed;
    - by Nakayama, V is free of rank one over Λ/3^{2k};
    - S−1 is right multiplication by c, with c² = 0;
    - `quat_sq_dvd` (rv-a6-route) gives c ∈ 3^kΛ.
  - The transport from the multiplicative CommGroup statement goes through `AddMonoidHom.toZModLinearMap`.
- `GlueA6Alg.Alg.exists_valuationSubring_comap_eq` (Extend.lean, and in A6.lean): for any field
  extension L/K and any valuation subring O of K, some valuation subring w of L has w ∩ K = O.
  It takes about 25 lines on top of Mathlib's `IsLocalRing.exists_factor_valuationRing`
  (Chevalley's extension theorem, Stacks 00IA).
- scratch/glue-a6-alg/A6.lean is rv-a6-route's A6.lean with the namespace renamed and the leaves
  unchanged (checked with diff). It adds:
  - `goodReduction_of_QM_rational3`: hypotheses hNOS, hRay, hTors, no hAlg;
  - `goodReduction_of_QM_rational3'`: also drops the auxiliary w and hw.

**Remaining:** nothing for A6 itself. The I2 leaves are still hypotheses, and their faithfulness
was reviewed elsewhere (pkg-I2, rv-a6-route). The move into ZInQKernel/ is left to the integrators.
Report: docs/research/glue-a6-alg.md. Log: scratch/glue-a6-alg/log.md.
