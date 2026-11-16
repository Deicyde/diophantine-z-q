# bg-explicit results log

Base 43513d87 (leaf-fold25). Field: `OpenResearchLeaves22.babaGranathRationalAb : HDec.QMSplit.Moduli.BabaGranathRationalAb` (TailZ22.lean:91).

## Findings
- VERIFIED (read): the field's only content beyond `ElkiesEquationsX6Ab` (= `ElkiesX6StarPrinted` via gt-elkies' proved
  `elkiesEquationsX6Ab_of_printed`) is the converse CM clauses (`π(x) = t₄ → HasCM4`, etc.), i.e. existence of
  CM points of the three types (cf. kernel `cm_of_val`, Leaves.lean:200).
- VERIFIED (read): `HDec.HeckeRest.ALFixedPoints` (TailG.lean:9485) is a theorem from textbook fields:
  `QMSplit.Aut.rows_of_C (QMLattice.qmCentralizerCMC_of uniformizationLeafAll gagaMorphism mumfordTorsionAlgClosed) T11b`
  (TailU.lean:1526, Contrib/OneProof/QMLattice.lean:507, T11b from HSyn.t11bExists_lf8, TailZ4.lean:60).
- Method: on Elkies' conic model (`X6Glue.conicModelT_of_charts`, TailZ21.lean:1353) the fibres of `t` over 1, 0, ∞
  have two points each ((±i,0), (0,±√−3), [1:±√−3:0]); the 4 Atkin-Lehner images of a point lie in its fibre, so two
  coincide, so `P ≅ P.twist (rep c)`, c ≠ 0 (rep_rep, xr), so P has CM (ALFixedPoints); Elkies' forward CM values
  exclude the two wrong types.

## Compile log
- scratch/bg-explicit/BGExplicit.lean: first full draft compiled (no errors) 2026-11-15 ~06:10.
  (Needed lean/.lake copied from ~/dzq-wt/cm-stab, same lean/ZInQ tree 02e27597.)
- ZInQKernel/Contrib/OneProof/BabaGranathRationalAb.lean: `lake build ZInQKernel.Contrib.OneProof.BabaGranathRationalAb` OK.
  `#print axioms` (scratch draft): both theorems [propext, Classical.choice, Quot.sound]. VERIFIED.
  (`local notation` replaced by selective `open ... (rep)`, `open ... (xr)`: kit forbids new notation.)
- #discharges (scratch/bg-explicit/discharges.txt): `DISCHARGES [OpenResearchLeaves22.babaGranathRationalAb]` by
  `babaGranathRationalAb_of_AL` and `babaGranathRationalAb_of_printed`; the latter assumes only open fields
  (elkiesX6StarPrinted, uniformizationLeafAll, gagaMorphism, mumfordTorsionAlgClosed); standard axioms. VERIFIED.
- autofold dry-run: strict 46/10 on 56 -> 45/10 on 55; strictest 45/11 -> 44/11. Generated module
  (FoldDryRun.lean) compiles, sixContactMin_of_open30 standard axioms. VERIFIED.
- New leaves: none.
