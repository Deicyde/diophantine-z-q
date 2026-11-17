# elkies-print results log

Base: wip/elkies-print at 5e235a40, merged origin/main c1e4ed1b (wip/integrate-w82 already on main).

## Target
Field `elkiesX6StarFunctionField : HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField`
(ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean L814), bundle OpenResearchLeaves28 (TailZ45).
kinds.tsv row 9: consequence, GLUE/GLUE; re-rated 11-16: "it carries the same R1 moduli witness rated composite
elsewhere (queue2 verdict)". VERIFIED (read).

## Findings
- F1 (VERIFIED, read): the Lean statement is `∃ Y Φ X Ψ fY t, R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ FF ∧ CM ∧ charts`:
  the existence of the moduli witness (fine Y3 with R1fpPropsAb, coarse X6 with X6Props) is bundled with Elkies'
  coordinate statement. No print states the witness (same shape as gonzalezRotgerX6Ab, rated composite).
  Not about explicit equations alone: no kernel computation can prove it.
- F2 (VERIFIED, read): precedent GRCountX6.GonzalezRotgerProp56X6: the print restated for every witness (no
  existence), the witness taken from the field gonzalezRotgerX6Ab of the same bundle.
- F3 (VERIFIED, read): kernel pieces for pinning the witness: compare_iso (TailU, R1fpProps version), x6Props_transport,
  coarseFactor_of / FactorThroughSurj (TailZ20), CurveBijIso (proved, curveBijIso_lf7), ShimuraSplit.pairsLift_of_T5.
- F4 (coordination, 11-16 16:10): task grx6ab-print folds gonzalezRotgerX6Ab and builds the witness as
  `GRX6AbPrint.x6ModuliWitness_of_coarse : ShimuraMainThmIDeligneY3AbU → X6CoarseModuli → GRDict.X6ModuliWitness`, whose
  body is identical to my `X6WitnessAb` (same binders). So my discharge takes the witness as a hypothesis `X6WitnessAb`;
  whichever fold goes second uses `_of_coarse` (after their fold gonzalezRotgerX6Ab leaves the bundle).

## Compile log
- C1 ElkiesPrint.lean v1 (leaf ElkiesX6StarEvery, X6WitnessAb, discharge, ffMap/ffMap_germ/ffMap_comp/ffMap_id): compiles (VERIFIED).
- C2 transport section (AL conjugation, fixedByW_eq_image, ff_transport, cm_transport, charts_transport): compiles (VERIFIED).
- C3 pinning (phi_part_ab, compare_iso_ab, coarse_compare_ab) and the converse `every_of_functionField :
  ElkiesX6StarFunctionField → ObjBridge.TorsionStructure → ElkiesX6StarEvery`, `every_iff_functionField`: compile.
  #print axioms on elkiesX6StarFunctionField_of_every, every_of_functionField, every_iff_functionField:
  [propext, Classical.choice, Quot.sound] (VERIFIED, scratch/elkies-print/Axioms.lean).
- C4 contribution ZInQKernel/Contrib/OneProof/ElkiesX6StarEvery.lean compiles (lake env lean, no warnings).
- C5 lake build +Main +Discharges +ElkiesX6StarEvery: 14102 jobs, success; frozenTarget standard axioms.
- C6 #discharges: elkiesX6StarFunctionField discharged by elkiesX6StarFunctionField_of_every (assumes ElkiesX6StarEvery,
  X6WitnessAb) and by ..._of_every_gr (assumes ElkiesX6StarEvery, GonzalezRotgerX6Ab); standard axioms (discharges.txt).
- C7 autofold dry-run: strict 16/21 on 37 -> 17/20; strictest 16/21 -> 17/20. FoldDryRun.lean (line 1 stripped) compiles;
  sixContactMin_of_open39 standard axioms.
