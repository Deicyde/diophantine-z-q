# loc-adopt: the locator audit applied to the notes and the TYZ docstrings

Task loc-adopt, 2026-11-12. Input: `docs/research/locators.md`, a primary-source audit by AI agents
with web access (not a human review). Base: 6988c7fe. Log: `scratch/loc-adopt/log.md`.

## Result

The audit's corrections are applied where it read the primary text, and its UNVERIFIED marks are
kept. No mathematical argument was changed. Every note says "read by the audit" and does not
claim a human check. No more than a line of any paper is quoted.

- **h-decomposition.md.** §0 has a dated paragraph on what the audit changed, and each list item
  has its corrected locator and status. §2:
  - **R2 restated.** `V/W ≅ P¹_ℚ`, with the polarized moduli identification. The degree-4 map
    `V → V/W` has ramification index **2** at each of `0, ∞, −16/27`; `4, 6, 2` are the
    orbifold elliptic orders. The Baba–Granath locators the audit read are recorded.
  - **R3.** The locator is Lin–Yang arXiv v1 **Example 29** (discriminant 6), not Example 30
    (discriminant 14). The journal numbering is unread. Baba–Granath Prop. 3.6 (p. 742) is an
    alternative supplier.
  - **R5 corrected.** The count is `#CM(R) = 2^{#{p | D(R)N(R)}}·h(R)` on `X₀(D,N)`; it is `h(R)`
    only on one orientation branch (the −19 and −24 examples are included). The fields of
    definition hold on `X₀(D,N)`.
  - **Other leaves.** Locator and qualification notes for R1, R6-R22:
    - Berger: arXiv v3 Thm 0.6, published Thm 0.7.
    - Pan: the `p = 3` residual exception and the Frobenius/dualization conventions.
    - Kato: the all-level supplier of R13.
    - Carayol: covers `p | N` and `ℓ = 2`.
    - Gaudron–Rémond: the constants, and the degree for a pair is the maximum.
    - Pazuki: Deligne's metric, `h_D = h_F + log π`, so `X_D ≥ max(1, h_D)`; the hardened `+3`
      covers it.
    - Unread originals stay UNVERIFIED.
  - **Route K.** Notes on K1-K4. Kisin 2009 Cor. 0.3 is a published alternative to Ribet. K4 can
    be dropped because Carayol covers `ℓ = 2`, which gives 19 leaves on route K.
  - **T27.** The locator is Chia-Fu Yu 2013, Thm 1.1, with "indefinite" kept.
  - §2.3 and §6 (R1, R2) are updated. No leaf count changed.
- **h-trust.md.** A header paragraph plus dated notes in A2, A5, A7, A10, C4, C7, C8, D2, D5,
  E2-E4, F1, F3 and §2.5.
  - **A2/A5.** The note says the branch-index correction may affect the argument. h-b1's M4 uses
    `4, 6, 2` as the indices of `Y₃ → P¹_j`, which is not the degree-4 cover the audit corrects.
    They would be the right numbers if the level-3 group is torsion-free modulo the centre
    (SPECULATIVE). The argument is not changed, pending the separate review.
  - **A10.** Same treatment for the CM count. h-cm and rv-h-cm already use `2^b·h(𝔬)`, which
    appears to match the corrected count (read, not re-derived). So the wrong `h(R)` was in the
    decomposition's R5 statement. Whether the count is applied to the right curve is for the
    review.
- **TYZ.** The convolution lemma is **Lemma 2.9** and the symmetry lemma is **Lemma 2.8**.
  - This is VERIFIED for arXiv v1 by recounting the environments that share the §2 counter in
    `Period7.tex`: the earlier notes skipped Definition 2.7 (`def primitive`, L842). The journal
    numbering is taken from the audit.
  - arXiv Theorem 1.2 is journal Theorem 1.4, with the "all `d_i > 1`" restriction kept, so the
    counterexamples apply to the journal theorem too (from the audit).
  - Fixed, with a dated note per file, in nt-tyz, cr3-trust, rv-tyz-inputs, pn-design,
    rv-pn-encoding, rv-prop-n, rv-nt-tyz, and in the docstrings and comments of
    `TYZInputs.lean` and `PropN.lean`. `LemmaTwoEight` keeps its name, and its docstring says it
    encodes Lemma 2.9.
  - **Extra finding** from the same recount, not in the audit: rv-tyz-inputs called `char'` and
    `multiples1` Lemmas 3.8 and 3.9; they are Lemmas 3.14 and 3.15 (fixed). `tyz-t1.md`, outside
    this task's scope, still says "Lemma 3.8" for `char'`.

## Checks

- `scratch/loc-adopt/check_code_unchanged.py` strips nested block comments, docstrings and `--`
  comments, normalizes whitespace, and compares each file with 6988c7fe. Result: **IDENTICAL**
  for `ZInQKernel/Hypotheses/TYZInputs.lean` and `ZInQKernel/RouteK/PropN.lean`. A negative
  control (a temporary rename) gave DIFFERENT.
- `lake build ZInQKernel` and `lake env lean scripts/print_axioms.lean`: see the next section.

## Build (VERIFIED, 2026-11-12, 01:17 PST)

- `lake build ZInQKernel`: "Build completed successfully (9925 jobs)", exit 0, no errors.
  `TYZInputs` and `PropN` rebuilt; there were warnings only (module-system import notes and one
  unused variable at `PropN.lean:1097`, which was there before this task).
- `lake env lean scripts/print_axioms.lean`: exit 0. Every one of the 91 "depends on axioms"
  lines lists exactly `[propext, Classical.choice, Quot.sound]`. That includes
  `ZInQ.PropN.tyzRow5b_of_tyzInputs` and the headline
  `..._of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier`. No `sorryAx`.
- The code-unchanged check, rerun after the build, gave IDENTICAL for both files.

## Not done / open

- The uses of R2's branch data (A5 via h-b1 M4) and of R5's count and fields (A10) are flagged
  for the separate review; they were not re-derived here.
- `Leaves.lean` docstrings (R2, R3, R5, T27 "indefinite", R14 Eisenstein case) are outside this
  task. They still carry the old statements and locators.
- `tyz-t1.md`, glue-repo, hdec-*, pkg-I1, wk-h, rv-leaves-a, h-b1 and h-v14 still cite "Lin–Yang
  Example 30", "indices 4, 6, 2" or "Lemma 3.8"; they are outside this task's edit list.
