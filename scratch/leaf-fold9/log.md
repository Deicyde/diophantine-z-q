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

## 11:45 lemmas compiled
- `lake build +ZInQKernel.OneProof.Main` on the base: exit 0 (base build log kept outside the repo).
- DumpCompact on the base: 10831 constants, identical to scratch/leaf-fold8/hashes_after.txt (hashes_before.txt).
- scratch/leaf-fold9/test/R1recT.lean COMPILES (lake env lean, ~5 s, no errors): specMap_comp_eq_self_iff,
  fixedField_le_of_le (InfiniteGalois), unramifiedAbove5_mono (discr_dvd_discr), isBaseChangeOf_of_iso,
  fieldOfModuli3_le, isBaseChangeOfPair_of_iso, unitPt, qmIso_of_isBaseChangeOfPair (rigidityHom),
  residueImage_eq_fieldOfModuliPair. VERIFIED.
- TailZ5 generated (mk_tailz5.py, 21 KB). Building CloudW07 (714 vendored files) first.

## 12:10 TailZ5 + Main (folds: r1r2-bridge, cloud PR #11) — VERIFIED
- CloudW07 JacobianExists + NormalModel built (lake build, exit 0).
- TailZ5 built after one fix (r5fp_of_rep: `rw` motive error through R5ptProps' auxiliary proof; replaced by
  IntermediateField.equivOfEq transport). 20.6 KB.
- `lake build +ZInQKernel.OneProof.Main`: exit 0; frozenTarget axioms [propext, Classical.choice, Quot.sound].
- DumpCompact: 10907 constants; cmp_hashes: 0 removed, 1 changed (frozenTarget), 76 new, all in TailZ5.
- Check9.lean: sixContactMin_of_open9 standard axioms; closure 212147 constants, no sorryAx; 62 fields
  (29 + 18 + 14 + 1), 20 with a kernel head constant; axioms of the two W07 proofs and of the bridge theorems standard.
- Counts (mk_fields9.py): 66 -> 64 -> 62 fields; strict LEAF/GLUE 39/27 -> 39/25 -> 37/25; lenient 55/11 -> 53/11 -> 51/11.

## 12:15 fold (4) modular-split (its .fleet report appeared) — VERIFIED
- `git merge origin/wip/modular-split` (clean). Folded only r15: `ModularSplit.deligneSerreConseq_of_ds` from the
  existing field dsThm966 (strict GLUE -1). Not folded: dimJacobianEqGenus (comp -> project glue
  H0DifferentialsEqHolo: neither count lowers), r17 (c -> c), eigenformHTNew (c -> c + glue HTDual: rises).
- Restructured: TailZ5 = lemmas + r1rec_of_rep/r5fp_of_rep (14 KB); TailZ6 = R15.lean verbatim + bundles (15 KB).
  Main imports TailZ6.
- Main build exit 0, frozenTarget standard axioms; DumpCompact 10917, 0 removed, 1 changed (frozenTarget), 86 new in
  TailZ5/TailZ6; Check9: 61 fields (28+18+14+1), closure 212153, no sorryAx; verbatim_check9 True/True.
- Counts: 61 fields, strict 37/24, lenient 51/10.
- reduct-split, shimura-split: still no .fleet report (12:15).
