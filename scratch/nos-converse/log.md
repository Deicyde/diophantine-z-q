# nos-converse log

Base wip/nos-proof e9828e92, merged origin/main e41a7169 (STATUS.md only). Build tree copied (reflink) from
~/dzq-wt/nos-proof/.lake/build and lean/.lake/build (same tree as base). Started 11-16 14:50 PST.

## Statement (verbatim, ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean l. 332)
`NOSProof.NOSConverseSep`: K field, O DVR, Ks IsSepClosure, w over O, A abelian variety (Grp form);
{m | 0<m ∧ IsUnit (m:O) ∧ InertiaTrivialOn A w m}.Infinite → HasGoodReduction A O.

## Findings (reading of the bundle fields; VERIFIED by reading the Lean statements)
- Open fields that construct a scheme over a DVR: only `neronSchemeExtensionExists` (OpenTextbookLeaves12),
  stated over 𝓞_L for L a NUMBER FIELD. With gt-blr's proved BLR 1.2/4 it gives Néron models over every DVR of a
  number field (`GapNeron.neronSchemeModelExistsNF`, NeronDVR.lean). Every other Néron/SGA7 field
  (raynaudSemistableSH, sga7_IX_3_3_SH, sga7_IX_3_5_ForwardGeom, neronBaseChangeStrictHenselization) is
  conditional on a given Néron model. `ReductSplit.NeronSchemeModelExistsDVR` (BLR 1.4/3 over any DVR) is not a field.
  => NOSConverseSep for a general K (e.g. K = C((t))) is not derivable from the bundles: no field produces an
  abelian scheme over such O.
- `shimuraIntegralModelRep` (the only integral-model field for QM surfaces) was pruned at sgr-fold (TailZ39), so
  the consumer cannot get good reduction from a proper integral Shimura model either.
- No field gives l-independence of inertia (GrothendieckMonodromy/RaynaudCriterion only give (σ-1)^2 = 0).

## Lean (scratch/nos-converse/Reduction.lean) — compiles 11-16 ~15:40, standard axioms (VERIFIED)
- `NOSConverse.nosConverseNF_of_pieces : NeronSchemeExtensionExists → NeronBaseChangeStrictHenselization →
  RaynaudSemistableSH → InertiaFixedRational → TorusRankZero → AbelianReductionGood → NOSConverseNF`.
- `nosConverseBar_of_pieces`: same over every field with `ReductSplit.NeronSchemeModelExistsDVR` (BLR 1.4/3 over any
  DVR, not a field) in place of N1. `neronOggShafarevich_of_bar : NOSConverseBar → r7a`; `bar_of_sep`.
- `goodReduction_of_QM_rational3_of_algNF`: the live consumer with `NOSConverseNF` in place of r7a (compiles).
- Pieces: InertiaFixedRational (GLUE, Galois: inertia-fixed torsion rational over the inertia field),
  TorusRankZero (GLUE, Serre–Tate torsion count on the semistable special fibre), AbelianReductionGood (LEAF,
  N⁰_{k̄} abelian ⇒ good reduction; properness criterion).
- `isInertia_of_fixes` (σ fixing the inertia field E pointwise is inertia at w) and `inertiaFixedRational_proof`
  PROVED (compiles, standard axioms): GLUE InertiaFixedRational closed.
- Contrib file ZInQKernel/Contrib/OneProof/NOSConverseReduction.lean: lake build OK (20 s), standard axioms.
- #discharges (scratch/nos-converse/Discharges-output.txt, VERIFIED):
  DISCHARGES [OpenResearchLeaves26.r7a] by NOSConverse.neronOggShafarevich_of_two
  still assumes [ReductSplit.NeronSchemeModelExistsDVR, GapSHPair.NeronBaseChangeStrictHenselization,
  ReductGlue.RaynaudSemistableSH, NOSConverse.TorusRankZero, NOSConverse.AbelianReductionGood]; standard axioms.
- autofold.json dry run (autofold-dryrun.txt): "strict count: 34/11 on 45 -> 34/13 on 47; strictest 34/11 -> 34/13";
  refused (GLUE rises). Not a fold candidate: keep nos-proof's NOSConverseSep.
- TorusRankZero decomposed (compiles, standard axioms, ~16:30):
  `torusRankZero_of_glue : TorsionInjectsSpecialFibre → ComponentIndexBound → DimensionRelation →
  NeronSpecialFibreComm → MumfordTorsionAlgClosed → TorusRankZero`; PROVED pieces: `semiAbelianTorsionBound_of`
  (#U(k)[m] ≤ m^r·m^{2a} from Mumford, U(k)[m] ↪ B(k)[m] × μ_m^r), `rankZeroAbelian_proof` (r = 0 ⇒ π flat
  surjective mono lfp ⇒ open immersion ⇒ iso ⇒ U proper), the counting assembly `torusRankZero_of_count`.
