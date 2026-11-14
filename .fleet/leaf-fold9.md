# leaf-fold9 (2026-11-14): fleet summary

**Result.** `ZInQ.OneProof.frozenTarget` now goes through `HDec.HSyn.sixContactMin_of_open9` (`OneProof/H/TailZ9.lean`).
The H bundles have 63 fields: 30 research, 18 textbook, 14 added, and 1 glue. Strict LEAF/GLUE is **42/21**, down from
39/27 at leaf-fold8's 66 fields. Lenient is 53/10, down from 55/11. Report: `docs/research/leaf-fold9.md`. Log:
`scratch/leaf-fold9/log.md`.

**Folds taken** (each lowers the strict GLUE count, and no count rises):
- **this task's Lean:** `r1rec` (R1(d)) and `r5` (R5) are theorems of the field `r1r2` (`TailZ5`: `r1rec_of_rep`,
  `r5fp_of_rep`). On the witnesses, the field of moduli equals the residue field. This uses infinite Galois theory,
  `discr_dvd_discr` for subfields, and uniqueness of base change via the kernel's `rigidityHom`.
- **cloud PR #11:** the fields `t33` and `normalModelOfFunctionFieldQ`, both proved.
- **modular-split** (merged): `r15` from the existing field `dsThm966`.
- **reduct-split** (merged): `r7b`, `r8` from four published-form leaves (Serre–Tate Thm 2; SGA 7 IX 3.6 and 3.5;
  BLR 1.4/3 over a DVR). No glue.
- **shimura-split** (merged): `r5count` from `GonzalezRotgerCountX6` (González–Rotger Prop. 5.6 on the canonical X₆).

**Not taken** (they would raise a count or leave both unchanged; report §5):
- mcr-quot: six L-leaves and two new glue Props in place of one.
- coarse-factor: `ConicCanonical` is `X6ConicModel` verbatim, and the H-1 route conflicts with the bridge.
- reduct-split's r6, SS1–SS3: each adds a project glue Prop.
- modular-split's dimJacobianEqGenus (comp → project glue), r17, eigenformHTNew.
- shimura-split's full bundle: 6 of its 9 leaves are consequences. Its y3Connected step (comp → c) leaves the strict
  count unchanged.

**Compiles (VERIFIED).**
- `lake build +ZInQKernel.OneProof.Main` exits 0, and `frozenTarget` has axioms [propext, Classical.choice,
  Quot.sound].
- DumpCompact/cmp_hashes: 10831 → 11123 constants, 0 removed. The only changed constant is `frozenTarget`, and every
  new constant is in TailZ5–TailZ9.
- Check9: the closure has 212 241 constants and no sorryAx.
- The copied files are verbatim (`verbatim_check9.py`).
- Each module is under 150 KB (TailZ7 is the largest, at 92 KB). No existing module or statement was edited.

**What remains.**
- Strict GLUE 21: 11 consequences, 9 composites, and the glue `QuotientP1Coordinate`.
- Next candidates:
  - prove `FixedTorsionRationalImperfect`, so that r6 pays;
  - turn shimura-split's Deligne π₀ / Baba–Granath leaves into printed form, so that r1r2 and y3Connected pay;
  - prove modular-split's `H0DifferentialsEqHolo`, so that dimJacobianEqGenus becomes a theorem.
- RISK: Serre–Tate Thm 2 may be printed only for complete K (reduct-split §5).
