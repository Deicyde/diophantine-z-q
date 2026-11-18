# c8-conrad3 (2026-11-17)

**Result: the three open glue Props of the C8 reroute are proved.** Each theorem has the statement verbatim as
its type, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`:
- `TwistCharHTWt0` (on-the-spot), proved as `HDec.G0Galois.C8Conrad.twistCharHTWt0_proof` in `Contrib/OneProof/C8Twist.lean`.
  - Chebotarev gives `tr r = ψ tr ρ_g`, hence `det r = ψ² det ρ_g`.
  - Hodge–Tate data in Tate–Sen coordinates give `y ≠ 0` with `σ(y) = ψ(σ)² y`.
  - `√y` in `ℂ_p` plus continuity of the orbit map make `ψ` Hodge–Tate of weight 0.
  - No new cited input, and `r` need not be semisimple.
- `InertiaAtPDecomp`, proved as `…inertiaAtPDecomp_proof` in `C8Dicts.lean`: conjugacy of places, G15's lift to
  `G_{ℚ_p}` (copied in `C8Ladic.lean`, because G15's file cannot be imported next to the chain), compactness, and Tau
  Ceti's root-of-unity criterion for inertia.
- `MinkowskiInertiaQ`, proved as `…minkowskiInertiaQ_proof` in `C8Dicts.lean`: inertia lifts from `Gal(F/ℚ)` to places
  of `ℚ̄`, then Mathlib's `exists_not_isUnramifiedAt_int_of_isGalois`.

**C8 now rests on two leaves.** `C8Printed.g12DetPZ_of_printed` derives C8's consumer from:
- `conradAppBQp`: **CITED** (L761, bibitem L11046);
- `tateTwistInvariantsInertia`: **DEPARTURE** (no Tate 1967 in the bibliography; it proves the uncited step L763-764).

`poincareComplement` is **ELLIOT** (L865 names the theorem and cites nothing). PR #86's
`CloudR2Poincare.poincareComplement_proof` has exactly the type `t8_of_poincareComplement` consumes; I checked this
by reading the branch and did not merge it.

**What compiles.**
- `lake build ZInQKernel.Contrib.OneProof.C8Printed` succeeds.
- Hand-fold dry run over the merged top (`sixContactMin_of_open72`), standard axioms:
  `scratch/c8-conrad3/C8FoldDryRun.lean`, with tops `frozenTarget_c8` and `sixContactMin_of_open73C8`.
- `#discharges`: 34 open hypotheses, 19 discharge one, none of them C8 (expected).
- Field taint: the Picard rows reach only consumer (iii) (`hodgeTateDecompAbVar → r10`).

**Counts.**
- The C8 part alone adds 2 rows and 0 glue Props (c8-conrad2's version added 5 rows, 3 of them glue).
- At the joint fold with the Hodge–Tate reroute, with PR #86: rows 0 and GLUE 0 while the two new leaves are pending
  review; GLUE −2 once they are rated LEAF. So net GLUE ≤ 0 is met.
- Do not fold alone.

**What remains.**
- Consumer (iii), the Hodge–Tate reroute (task derham-scholze).
- Page reads of Conrad App. B, Tate 1967 §3.3 and Milne 1986 (the unread flags are kept). If Conrad App. B states that
  the exponent equals the Hodge–Tate weight, the DEPARTURE leaf can go.
- Report: `docs/research/c8-conrad3.md`; spec: `scratch/c8-conrad3/autofold.json`.
