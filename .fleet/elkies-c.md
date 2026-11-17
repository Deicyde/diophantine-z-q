# elkies-c (fleet summary)

**Result.** Step (c) of the Elkies row and the reviewer's `HasCM` step are now proved glue. New file
`ZInQKernel/Contrib/OneProof/ElkiesX6StarCM.lean` (namespace `ElkiesC`, imports `X6AtkinLehnerIdeal`) with helper
`ElkiesC/ClassNumber24.lean`. The new leaf `ElkiesX6StarOneIdeal` is x6-coarse's `ElkiesX6StarEveryIdeal` with its
CM clause in the weakest printed reading: *some* point with `HasCM24` / `HasCM4` / `HasCM3` sits at `t = 0, 1, ∞`.
`elkiesX6StarEveryIdeal_of_one` proves the every-point form from that leaf plus the three textbook fields, which
are already proved in the tree. The proof, per discriminant:
* exactness `HasCM_D ⇔ End_𝒪(A) ≅ R_D` via the lattice model (`hasCM*_iff_com`), and equivalence with
  González–Rotger's CM points (`hasCM*_iff_isGRCMPoint`). This is the reviewer's deciding step;
* `#CM(R_D) ≤ 2` from `EichlerBound.r5fpCountLe_proof`, with **h(ℚ(√−6)) ≤ 2 proved** (Minkowski,
  `discr = −24`, `𝔭₂² = (2)`, `𝔭₂𝔭₃ = (√−6)`) and `inertCount6 ℚ(√−6) = 0`;
* Galois stability of the `HasCM_D` points, from the Galois clause of `X6Props`;
* Elkies' charts put `√−1` or `√−3` in the residue field over `0`, `1`, `∞`, so the conjugate is a different
  point. The rational value of `t` then spreads to both points.
Counting route used; the stabilizer route was not (the tree lacks the `W`-action on CM points).

**Compiles (VERIFIED).** Both files build; all 89 declarations use only the standard axioms. `#discharges`:
`elkiesX6StarEvery` is discharged by `ElkiesC.elkiesX6StarEvery_of_one_twist`, still assuming
`ElkiesX6StarOneIdeal`, `X6CoarseModuli`, `ShimuraMainThmIDeligneY3AbU` and the three proved textbook fields.
Autofold spec `scratch/elkies-c/autofold.json`: count stays 15/16 → 15/16, because the new leaf is a consequence
and pending review. The generated fold module compiles with the standard axioms.

**Remains.** Step (a), `ℚ(X/W) = ℚ(X)^W`, is with another worker; once it is done the leaf could be rated printed
form. The reviewer's queue10 note was not found in the repo, so I worked from the task's quote of its deciding
step. Report: docs/research/elkies-c.md; checks: scratch/elkies-c/.
