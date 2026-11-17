# group-law results log

Base 0caafe66 (wip/group-law). Build tree copied from the gaga-serre worktree (base + Contrib files only);
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordRigidity`
replayed 13698 jobs, frozenTarget standard axioms (VERIFIED, 11-16 12:31).

## Statement
- Field `mumfordGroupLaw : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw`
  (ZInQKernel/Contrib/OneProof/MumfordRigidity.lean L82), in OpenResearchLeaves26 (and every generation 14..26).

## Consumers (VERIFIED, scratch/group-law/ClosureCheck.lean -> closure_check.txt)
- Direct users in frozenTarget's closure: only `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw`
  (TailZ40), called by HDec.HSyn.x6Rows_of_open14, researchLeaves9_of_open14 (TailZ23) and
  DCY3Used.y3Connected_of_leaves (Contrib, via TailZ34). So the chain needs only
  `QMFamilyGroupLaw` (S proper smooth curve over Q, F a QMFamily with QML3 field fibres).
- rigid-prune's sites N1 (MCRGlue.QuotientP1Coordinate, modelCoordinateResidue_of_quotient') and
  N2 (HDec.ModelGlue.exists_genFib_to_Y, heckeVertWitness_of_curveBijIso) are NOT in the closure any more.
- RigidScan (rigid-prune's scan rerun, scan_*.txt): 34 constants mention R1univProps in their value;
  new since rigid-prune: SGRDirect.elkies_coordinate (univ applied to Elkies' family obtained from an
  Ab clause: fine on abelian schemes) and GapST.cm_pointW (destructures R1fpProps; no univ application in
  its source text). Non-Ab R1fpProps occurs in field types only of old generations (OpenResearchLeaves<=9,
  OpenAddedLeaves<=8, OpenGlue<=7): current bundles carry only Ab forms.

## Lean: ZInQKernel/Contrib/OneProof/GroupLawGlue.lean (VERIFIED compiles, `lake env lean`, 11-16 ~15:30)
- `isAbVarFibre_of_isPullback`, `fibreHyp_of_isPullback`: fibre hypothesis passes to base changes.
- `LocalLaw F e`: open immersion j : T → S, base change P of F along j with GrpObj, identity = base change of e.
- `mulP_pt`, `invP_pt`: on field points the local law is the fibre abelian variety's law
  (via the chain's `isGrpFibre_of_rigidity`).
- `glue_of_rel`: gluing over the cover by preimages of the local opens, compatibility on field points of
  reduced overlaps (`hom_ext_pts`).
- `exists_grpObj_of_localLaws`: [IsReduced F, F⊗F, (F⊗F)⊗F], e section, FibreHyp, local laws through every
  point ⇒ ∃ GrpObj F, η[F].left = e. No sorry.

## Lean: spreading, stalks, final (VERIFIED compile, 11-16 13:00-14:45)
- GroupLawStage.lean: `exists_grp_stage_Q` (spread-out's exists_grp_stage carrying a stage invariant).
  Needs `set_option backward.isDefEq.respectTransparency false` (as Spread.lean) or the Over.pullback
  monoidal instance is not found.
- GroupLawSpread.lean: `exists_stage_law` (generic cofiltered limit), `localLaw_of_stalk`
  (group law on F ×_S Spec Γ(S,V)_𝔭 with identity e ⇒ LocalLaw through the point 𝔭).
- GroupLawStalks.lean: `grpObj_of_stalkLaws` (gluing), `stalkData`, `grpObj_of_isField` (field base: outright),
  `isDomain_of_maximalIdeal_eq_span`, `stalk_field_or_dvr` (smooth rel. dim 1 over a field: stalks are
  fields or DVRs), `field_or_dvr_localization` (same for Γ(S,V)_𝔭).
- MumfordGroupLawRed.lean (final): leaves `MumfordGroupLawDVR`, `MumfordGroupLawLocal`;
  `local_of_field`, `dvr_of_local`, `dvr_of_field` (new leaves never stronger than the field);
  narrowed forms `MumfordGroupLawCurve`, `MumfordGroupLawRed` (+ `curve_of_field`, `red_of_field`);
  `mumfordGroupLawCurve_of_dvr`, `mumfordGroupLawRed_of_local`;
  `LeafQM.AV.R1UnivRigid.exists_qmAbScheme_of` (rigid-prune's proof, verbatim, hypothesis = group law over S),
  `qmFamilyGroupLaw_of_curve`, `qmFamilyGroupLaw_of_dvr`, `qmFamilyGroupLaw_of_local`.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordGroupLawRed`:
  13703 jobs OK (13704 after GroupLawLocDiagram; rerun 2994 theorems checked). scratch/group-law/Discharges.lean → discharges.txt: `#discharges` finds 7 discharges, none by the
  new file (expected: no new theorem has type `MumfordGroupLaw`); all new main theorems standard axioms.

## Verdict so far
- `mumfordGroupLaw` NOT removed (no −1). The field as stated (all locally noetherian S, non-reduced included)
  is not proved. The chain's need (QMFamilyGroupLaw) is proved from GIT 6.14 over a DVR (`MumfordGroupLawDVR`),
  a strictly weaker leaf (dvr_of_field). Replacing the field by it is a narrowing (count 0) that autofold cannot
  express (the old generations' field type is `MumfordGroupLaw`); manual fold like rigid-prune's.

## Narrowing fold check (VERIFIED, olean overlay outside the repo, 11-16 ~15:40)
- 13 patched modules (field type MumfordGroupLaw → MumfordGroupLawDVR in OpenResearchLeaves14..26; TailZ23 3 sites
  qmFamilyGroupLaw_of_dvr; TailZ34 y3Connected_of_ab_gl ... qmFamilyGroupLaw_of_dvr ...): scratch/group-law/fold/narrowing.patch.
- 31 downstream modules recompiled with `lean -R root -o` into /tmp/glfold/lib (symlink tree of the build,
  rebuilt modules replaced); all rc=0, 5-28 s each.
- Main: 'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound].
- FoldCheck: OpenResearchLeaves26.mumfordGroupLaw : … → MumfordGroupLawDVR; MumfordGroupLaw not in closure;
  MumfordGroupLawDVR, qmFamilyGroupLaw_of_dvr in closure.
