# leaf-fold9 results log

## 2026-11-14 11:25 start
- Base 5da857b0 (wip/w59). Fresh run (no earlier log).
- Fold (1) mcr-quot: decision by counting (see report §5): replacing the pg glue QuotientP1Coordinate by
  L1-L6 (L1, L3, L6 composites; L5 consequence; L2 special case; L4 STANDARD), P1SchemeQ, CMStabObj (new glue)
  and CoverModelOfHeckeN raises strict GLUE (-1 + >=6). NOT TAKEN.
- reduct-split, shimura-split: branches at base commit, no .fleet report yet; modular-split absent.
- Fold (2) coarse-factor, analysis (no Lean needed):
  - H-43: `ConicCanonical` has the same text as the field `x6ConicModel` (`X6Kummer.X6ConicModel`), and
    `x6ConicModel_of_canonical''` additionally needs r1r2; replacing the field is a renaming. NOT TAKEN.
  - H-1: `r1r2` (comp) -> `CanonicalCoarseX6` (carries the "qualified consequence" caveat: c), `BabaGranathX6`,
    `GonzalezRotgerX6` (published) and `ReciprocityOfFine` (glue). `CanonicalModelY3` is implied by any of the
    three existential forms. Strict GLUE -1 +1 +1 = +1, or 0 if ReciprocityOfFine were proved (from r1rec).
- Better route found: r1r2's witness already carries R1recProps and R5ptProps (on residue fields of points);
  the fields r1rec (R1rec, field of moduli of objects) and r5 (R5fp, field of moduli of pairs) follow from r1r2
  once residue field = field of moduli is proved on the witnesses. Drafted in scratch/leaf-fold9/test/R1recT.lean:
  fieldOfModuli3_le (fine witness, needs no rigidity, plus discr_dvd_discr for subfields), and
  residueImage_eq_fieldOfModuliPair (coarse witness, uniqueness of base change via kernel rigidityHom).
  This makes H-1 fold pointless (r1rec would be consumed) and lowers strict GLUE by 2 instead.
