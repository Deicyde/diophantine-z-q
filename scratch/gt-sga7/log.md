# gt-sga7 results log

Base ef2f6915 (wip/leaf-fold18, top TailZ29).

## Findings (reading)
- VERIFIED (read TailZ19 L249, L1595-1650): the field `CToPrinted.SGA7_IX_3_3` is SGA 7 IX 3.3 **second** assertion
  (N0 x R' -> N'0 open immersion with image N'0). Its one use (`identityComponentBaseChangeDVRRange_of`, inside
  `semistableNeronBaseChange_of_printed_full`) is at L number field, O = O' ∩ L, L'/L finite number fields; only the
  open-immersion half is used (`obtain ⟨hWo, -⟩`).
- VERIFIED (read TailZ23 L311-330): the chain's leaf `ReductB.SemistablePersistsSHcp` is the **first** assertion of
  SGA 7 IX 3.3 (semistable reduction persists). It does not imply the second assertion: a strictly henselian form of
  the second assertion is needed as a leaf.
- VERIFIED (git show origin/wip/sh-printed2): task sh-printed2 (11-14, base b5ff0474, not folded) proved
  `SGA7_IX_3_3_0` (char 0, perfect residue field) from `SGA7_IX_3_3_SH` + sh-route's `NeronBaseChangeSH` + SGA 3 VI_B
  3.10 + Stacks 04KV, by fpqc descent. Plan: port onto the current chain with GapSHPair (every characteristic).

## Lean (all VERIFIED by compilation)
- `ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean`: `lake env lean` 10 s, 8.5 GB, 0 errors, 0 warnings (11-15 01:47).
  Statements: `SGA7_IX_3_3_SH` (LEAF, SH on O and O'), `SGA7_IX_3_3_SHcp` (LEAF restricted, + CharZero K, perfect κ(O)),
  `SGA7_IX_3_3cp` (field + cp). Theorems: `sga7_IX_3_3_SH_of_field`, `sga7_IX_3_3_SHcp_of_SH`, `sga7_IX_3_3cp_of_field`,
  helpers (sh-printed2's, `pbCompIso_fst` via vendored `Over.pullbackComp_hom_app_left_fst_fst`), core `body_of_SH`,
  `sga7_IX_3_3_of_SH` (the field exactly), `sga7_IX_3_3cp_of_SHcp`, consumer reroute
  `identityComponentBaseChangeDVRRangeCP_of`, `semistableNeronBaseChange_of_printed_cp`, `semistableNeronBaseChange_of_SHcp`.
- `lake build +Main +Discharges +Contrib.OneProof.SGA7PersistsNF`: success (12933 jobs; module 8.3 s).
- `scratch/gt-sga7/Discharges.lean` (7.6 s): `DISCHARGES [OpenResearchLeaves19.sga7_IX_3_3] by
  SGA7PersistsNF.sga7_IX_3_3_of_SH`, still assumes `[SGA7_IX_3_3_SH, GapSHPair.NeronBaseChangeStrictHenselization,
  CToPrinted.SGA3_VIB_3_10, AVGlue.GeomConnOfRationalPoint]` (last three already bundle fields), standard axioms.
  All four `#print axioms`: `[propext, Classical.choice, Quot.sound]`. Output in `discharges-output.txt`.
- `autofold.py scratch/gt-sga7/fold-spec.json --dry-run`: `strict count: 49/12 on 61 -> 50/11 on 61; strictest 48/13 -> 49/12`;
  output minus line 1 = `FoldDryRun.lean`, compiles in 5.7 s; `sixContactMin_of_open24` standard axioms.

## Consumer sites (for the cp route, option B)
- TailZ23 L794 (`researchLeaves9_of_open14`, live path), TailZ19 L1894 (`researchLeaves11_of_open12`), TailZ19 L1775
  (`fields_of_leaves`, not on Main's path). Replacement term: `SGA7PersistsNF.semistableNeronBaseChange_of_SHcp`.
