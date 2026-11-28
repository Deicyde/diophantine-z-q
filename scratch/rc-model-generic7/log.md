# rc-model-generic7 results log

Base: aba99b7b2e3eea8804ebeffd1834ba5f31fa9c7e.

## Item 1 (doc fixes)
- (a)-(n) applied to docs/research/rc-model-generic6.md, docs/research/rc-model-generic5.md, .fleet/rc-model-generic6.md, .fleet/rc-model-generic5.md, scratch/rc-model-generic6/log.md.
- (g) CharFreeSeam.lean line 20 and (i) CharFreeSeamTwo.lean line 3: docstring only, line counts unchanged.
- Rebuilt RC/ModelGeneric6/CharFreeSeam and CharFreeSeamTwo: Build completed successfully; axioms unchanged (propext, Classical.choice, Quot.sound).

## Item 2 / 3 Lean modules (RC/ModelGeneric7/)
- Interface.lean: INTERFACE block (atkinLevelAlg, PointW, exactly as written), Wint_left, atkinLevelAlg_toRingHom, smulSubgroup_cyclic, smulSubgroup_div_cyclic.
- PairMap.lean: pointMapAlong, ptMap_eq_pointMapAlong, cyclicMap, enhancedMap, enhancedCurve_eq, quot_mk_eq_of_variableChange, pairClassesMap (+_mk, _id, _comp, _symm_apply, _injective), cyclicQuotientCurve_map (T2), shortCoverPair_comp, rationalPoints_comp, rationalPoints_ringEquiv.
- Y0Points.lean: Y0LevelPoints_comp_inclusion (copy of `equivalent`), exists_comp_inclusion, Y0LevelPoints_comp, Y0LevelPoints_algEquiv.
- Lift.lean: wittLocalAlgebra, exists_wittLift.
- SeamFormula.lean (R0): OddStepFormula, TwoStepFormula, StepFormula, FormulaSeam (inductive), exists_oddStep_formula, exists_twoStep_formula, exists_formulaSeam, exists_quotientSeam_of_formulaSeam.
- FormulaTransport.lean: formula maps, PtRel, stepRel, formulaSeam_rel, rationalPoints_atkinRat_formulaSeam (item 2 for R0 seams, no T3), atkinClass_independent_formulaSeam.
- Finding: item 2 for R0 seams needs no function-field transport (T3): R0 seams are determined by Vélu formulas, which commute with ring maps.
