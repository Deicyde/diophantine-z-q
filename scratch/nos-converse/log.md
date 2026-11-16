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
