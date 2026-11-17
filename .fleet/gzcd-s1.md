# gzcd-s1 (2026-11-17): hGZ in printed form, the three queue12 steps proved

**Result.** The binder `hGZ`'s current type `ZInQ.GZSch.GrossZagierCurveCd` is now **equivalent in Lean** to the
printed-form leaf `ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted` (`grossZagierCurveCd_iff_printed`; compiled, no
`sorry`, axioms propext/Classical.choice/Quot.sound). The leaf is Gross–Zagier I.6.3 / V Thm 2.1 for
`π : X₀(N) → E` on **one** normal proper model, with:
- `π(∞) = O` stated literally;
- `K` the imaginary quadratic field with `NumberField.discr K = D`;
- `p ∣ N` split in `K`;
- the twist by the character of `K`;
- any embedding `K → ℂ`.

How the queue12 steps are closed:
- **S1** (every model) and **G4(b)** (`V₊(Z) ∩ E = {O}`): h33-d1's model uniqueness and `not_mem_chartZ_iff`.
  I merged h33-d1 instead of duplicating it.
- **S2**: eps-splitting's `quadChar_eq_epsD`, plus my new **discriminant bridge**: `GZDiscr.discr_eq_of_sq`
  (`δ² = D` ⇒ `disc K = D`) and `GZDiscr.exists_sq_eq_discr` (every quadratic field contains `√disc`).

Rating: **LEAF, printed form**. Count: `hGZ` GLUE → LEAF, GLUE −1, no new glue. The remaining items are readings
only:
- the canonical model;
- the point `τ`;
- G10, the normalization of `ĥ`, absorbed by `∃ κ > 0`.

**What compiles (VERIFIED).**
- New files: `ZInQKernel/Contrib/OneProof/GrossZagierCdPrinted.lean` and `.../GrossZagierCdPrinted/Discr.lean`.
- Merged from h33-d1: 8 Contrib files.
- `lake build Main Discharges GrossZagierCdPrinted`: 16091 jobs, no errors.
- `#discharges`: `DISCHARGES [hGZ] by ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed`, standard axioms.
- Manual fold dry-run `scratch/gzcd-s1/FoldCheck.lean`: `frozenTarget_printed` on the current top
  (`sixContactMin_of_open63`), standard axioms, and `rfl`-equal to `frozenTarget` applied to the bridge.
- Autofold spec: `scratch/gzcd-s1/autofold.json`. It is a binder, so the fold is manual; the note gives the edit.

**What remains.**
- The integrator chooses between two options:
  - (a) keep the binder type and rate it by the equivalence;
  - (b) retype `hGZ` to `GrossZagierCurveCdPrinted`.
- A statement check of the leaf against the GZ print (no copy on this host; locators UNVERIFIED).

Report: `docs/research/gzcd-s1.md`.
