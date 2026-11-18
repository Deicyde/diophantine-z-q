# y3-p1j: leaf Y3ToP1j, the N-action on the integral model, R2 re-sourced to Y₃ → P¹_j

Task y3-p1j, 2026-11-17. Report: docs/research/y3-p1j.md (§1 is the Manuscript check). Log: scratch/y3-p1j/log.md.

**Main result.** New files `ZInQKernel/Contrib/OneProof/Y3ToP1j.lean` and `Y3ToP1jDescent.lean` (namespace
`Y3P1j`). Both compile with `lake build`, and every summary theorem uses only the standard axioms (VERIFIED).
* **(a) Leaf `Y3ToP1j`** (kind consequence, flag ELLIOT, tex L420-440). For every fine witness `(Y, Φ)` there is
  a `π : Y → P¹` with these properties:
  * its `ℚ̄`-fibres are the `Aut(𝒪)`-twist classes, i.e. the `N`-orbits;
  * the CM points of discriminants −4, −3, −24 are exactly the fibres over `0, ∞, −16/27`;
  * `π` is onto `P¹(ℚ̄)`;
  * every `ℚ̄`-fibre has at most 324 points.

  Rating: not printed form. `y3ToP1jAt_noDeg_of_row` proves that, against the chain's current leaves, only the
  degree bound is new.
* **(b) The N-action, proved from `Y3FullThreeRepZ30` (Yoneda).**
  * Twists by `Aut 𝒪` and `rightMul` by `𝒪^×` act on `QMAbSchemeP` over any base, printed level clause included.
  * They act by automorphisms of the `ℤ[1/30]` model, with the composition laws.
  * `−1` acts trivially.
  * Summary theorem: `action_of_z30`.
* **(c)** The quotient `P¹_j` has a source: Baba–Granath Thm 2.1 and Lemma 3.1 (`V/W ≅ P¹_ℚ`), cited at L420-422.
  The step `Sh_{K₃}/N = Sh_N` is an implicit standard step; the `j`-normalization is a Möbius choice.
* **(d)** `Descent.hauptmodulOfX6_of_y3ToP1j' : Y3ToP1j → HauptmodulOfX6`, and `Descent.r1r2W_of_y3ToP1j'` builds
  the row `R1R2fpRepW` with R2 from `Y3ToP1j` alone.
  * The descent of a `P¹`-map along `Y₃ → X₆` (`ToP1DescendsAlongSurj`) is proved. Ingredients: p1-quot's CloudW07
    `P¹` (copied); a new lemma that points are determined by their coordinate; the kernel's
    `factorThroughSurj_proof`.
  * No new glue.

**Not droppable (VERIFIED by grep, scratch/y3-p1j/grep-x6.txt).** `x6CoarseModuliIdeal` and
`elkiesX6StarEveryIdeal` are still read on this base:
* `x6CoarseModuliIdeal`: the row's `X₆` witness and González–Rotger `R5ptProps`;
* `elkiesX6StarEveryIdeal`: `x6ConicModel` → NoCM, and sgr-direct's `HeckeSqrtBranchAny`.

So no top field is discharged: there is no autofold spec or dry run. `#discharges` lists nothing for `Y3P1j`, and
the GLUE count is unchanged at 4/27 on 31. The kinds row for a later fold is in scratch/y3-p1j/kinds-rows.tsv; it would make the count 4/28 on 32.

**Manuscript check.**
* L412-418 Gram matrix: exact, det 1, VERIFIED.
* `|(𝒪/3𝒪)^×| = 72`: VERIFIED. So the printed `≤ 324` holds; the true degree is 144.
* L425-436: OK, with the implicit step at L434-436.
* Known issues, all already known: the indices 4,6,2 are orbifold orders; the `j`-normalization is not in BG
  Thm 2.1/Lemma 3.1; the bibliography cites the BG preprint; the polarization point from y3-route-a.

**Remains.**
* Dropping the X₆ fields needs more than this task:
  * restate the row over Y₃ (`R2fpProps`) so that it carries no `X₆` witness;
  * re-route its consumers on top of cm-branch;
  * re-route sgr-direct's `HeckeSqrtBranchAny`, which reads Elkies' `√−t`, to the manuscript's tame local
    equation (L517-526).
* Optional: the adelic ↔ moduli orbit dictionary (ON THE SPOT in the report) in Lean.
