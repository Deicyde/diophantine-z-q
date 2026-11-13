# rv-g0pieces: adversarial truth review of g0-split's ten glue pieces

**Verdict.** No piece is refuted.

- **TRUE (7):** `DimFinite`, `DimBaseChange`, `X1BelyiOnModel` (given `BelyiX1`), `ProductExists`,
  `ReverseIsogeny`, `StableHeightBaseChange`, `HeightAdditivity` (given that def-faltings agrees
  with the published height). `StableHeightBaseChange` can be proved from the definition, with no
  Néron model.
- **TRUE given Glazer §4:** `ModularConstituent`. Its bounds `[L':ℚ] ≤ QM` and `N ≤ QM²` match
  manuscript L713 and L857, and the model is produced together with the field.
- **UNSURE as stated, TRUE for the genuine triple:** `ThetaPointOfFibre` and `FibreSimple`. The
  same issue touches `ModularConstituent`, which is probably robust to it.

**Main finding.** These three pieces quantify over every `(Y, Φ, π)` satisfying `R1fpProps` and
`R2fpProps`. Those clauses do **not** pin `Φ`: naturality is only required under field maps, so
any residue-field-preserving bijection of the points of `Y` gives a natural relabeling, and the
relabeled triple still satisfies both clause lists (compiled). Such a relabeling can attach to a
point over `J(u)` the class of another rational fibre that is `ℚ`-isomorphic to it, for
instance a CM fibre, or one of much smaller height. Whether such fibre coincidences exist is
open. Either way, the pieces cannot be proved as glue in their present form.

**Repair.** Pin `Φ` by a universal family (`Y₃` is a fine moduli scheme), or add an F1 clause to
R2fp. As a stopgap, state the pieces for the leaf's own triple. Details in
docs/research/rv-g0pieces.md §4.

**Also checked numerically.** The constant `3779136` in `ThetaPointOfFibre` follows from
`I4⁵/I10² = (Σθ⁸)⁵/(Πθ²)²`, which holds to `1e-22` on two curves (`theta_igusa_check.py`). This
closes, numerically, the Igusa normalization that h-v14 left UNCHECKED; the `J ↔ I` conversion
used is STANDARD but recalled from memory. A check of NoCM against Elkies' 24 rational CM
values is consistent with A10 (`nocm_square_check.py`).

**What compiles.**
- `scratch/rv-g0pieces/Exotic.lean` (Split.lean 1-15140 plus two sections): 0 errors, standard
  axioms. It proves `r1fp_relabel`, `r2fp_relabel`, `r1r2_relabel`, `relabelPt_bijective`,
  `relabelPt_comp`, `relabelOver_natural` and `r1fp_exotic`.
- `ExoticCore.lean`: a Mathlib-only copy of the core, also 0 errors.

**What remains.**
- The arithmetic question: are two rational fibres of `Y₃ → P¹` (one over `J(u)`, `u ∉ 𝒞`)
  ever isomorphic as `ℚ`-schemes?
- Implementing the repair (QML3 over a base scheme).
