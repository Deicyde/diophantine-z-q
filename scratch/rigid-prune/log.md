# rigid-prune results log

- 2026-11-15 02:27 start. Base bb9b2e4d (wip/leaf-fold19). No earlier log.
- Base build `lake build +ZInQKernel.OneProof.Main` OK (exit 0). DumpCompact on base: 13675 constants,
  frozenTarget standard axioms (scratch/rigid-prune/hashes_before.txt).
- RigidScan.lean (closure of frozenTarget, 243455 constants): 85 defs built on R1fpProps, 245 non-generated constants
  typed with them (scan_typed.txt), 38 constants whose value mentions R1univProps (scan_univ_users.txt).
  Reading each of the 38 (decl_src.py): genuine applications of the universal clause are
  * phi_part and its users (compare_iso, exists_surjective_of_R1fp, kummerFibreEquiv_transport, sameTripleMor_of_mobius):
    univ of one witness on the family from R1fam of another: fine on abelian schemes (no rigidity);
  * QMSplit.Moduli.classify / heckeOfFine_proof (TailU): univ on twists of the universal family: fine on abelian
    schemes given the twist of a QMAbScheme;
  * ModelGlue.exists_genFib_to_Y (TailL L1645; users modelIntegral_of, modelFunctionField_of_curveBijIso ->
    heckeVertWitness_of_curveBijIso -> heckeVertWitness_of_leaves5): univ on famBC 𝒜 j, 𝒜 the family of the
    Shimura model given by the field shimuraGoodReductionNoGuard as a QMFamily only: NEEDS RIGIDITY.
  * the others destructure R1fpProps and drop the univ clause (false positives).
- Second genuine need: the TOP field OpenGlue7.quotientP1Coordinate (MCRGlue.QuotientP1Coordinate, TailW L202)
  has `R1fpProps Y Φ` as a hypothesis (its conclusion does not mention Y); its consumer
  MCRGlue.modelCoordinateResidue_of_quotient(') (TailX L275) must supply R1fpProps of some witness, which on
  abelian-scheme leaves needs R1univProps on all QMFamilies: NEEDS RIGIDITY unless the field statement changes.
- Verdict: mumfordRigidityCore cannot be pruned without changing field statements. Plan (partial result):
  merge gt-rigidity; prove QMFamilyGroupLaw (every QMFamily over a proper smooth ℚ-curve with object fibres underlies a
  QMAbScheme) from gt-rigidity's MumfordGroupLaw alone (GIT Thm 6.14 without Cor. 6.4: iota_hom proved fibrewise);
  re-version the on-chain conversions (TailZ23) through QMFamilyGroupLaw, so no mumfordRigidity_of_core remains on
  the chain and the chain's use of the field is exactly GIT 6.14 on QM families.
- TailZ40.lean compiles (lake env lean): isMonHom_of_fibres, exists_qmAbScheme_gl, qmFamilyGroupLaw_of_groupLaw (MumfordGroupLaw alone, no Cor 6.4), qmFamilyGroupLaw_of_core, r1fpProps_iff_ab_gl, nine *_iff_ab_gl; standard axioms.
- TailZ23 rewired: imports TailZ40; `mumfordRigidity_of14` deleted; `x6Rows_of_open14`, `addedLeaves9_of_open14`,
  `researchLeaves9_of_open14` use `*_iff_ab_gl (qmFamilyGroupLaw_of_core r.mumfordRigidityCore)`.
- `lake build +ZInQKernel.OneProof.Main` OK (2m53). ClosureCheck: mumfordRigidity_of_core, MumfordRigidity,
  exists_qmAbScheme, r1univProps_of_ab, r1fpProps_eq_ab' NOT in frozenTarget's closure; MumfordRigidityCore,
  QMFamilyGroupLaw, qmFamilyGroupLaw_of_core, MumfordGroupLaw, mumfordGroupLaw_of_core are.
- DumpCompact after: 13694 constants, frozenTarget standard axioms. cmp_hashes: removed 1 (mumfordRigidity_of14),
  new 20 (TailZ40), changed 3 (value only: x6Rows_of_open14, addedLeaves9_of_open14, researchLeaves9_of_open14).
  frozenTarget, every bundle and every sixContactMin_of_open* unchanged.
- PruneScan: 30 + 13 + 14 + 1 = 58 fields, 0 unused, prune set empty (mumfordRigidityCore still used).
- OpenStatements: 65 open hypotheses; render_open.py: 58 H, strictest 44/14; --check ok; no generated file changed.
- DischargesTest: the 5 earlier discharges and both controls (t1, t3 sorry) unchanged; 2 more, gt-rigidity's
  mumfordRigidityCore_of_printed / _of_pushforward (its Contrib module is now imported by the chain). Saved.
- scratch/rigid-prune/Sites.lean compiles: phi_part_ab (comparisons of abelian-scheme witnesses need no rigidity), ShimuraModelGenericAb + exists_genFib_to_Y_ab + shimuraModelGenericAb_of_gl (site N2 is an instance of QMFamilyGroupLaw), r1fpProps_of_ab_gl and the unfolded statement of QuotientP1Coordinate (site N1); standard axioms (sites_out.txt).
- docs/research/rigid-prune.md and .fleet/rigid-prune.md written; Main.lean comment updated; rebuild OK; hashes unchanged (13694, removed 1, new 20, changed 3).
