# raynaud-narrow results log

Base 5e235a40 (TailZ45, sixContactMin_of_open38); merged origin/wip/raynaud-proof (ee976e59) for
ZInQKernel/Contrib/OneProof/RaynaudSemistableCP.lean (consumers_of_cp_leaves).

## Consumers (grep, VERIFIED)
- `.raynaudSemistableSH` read only at TailZ23 L722 (`raynaudSemistable_of14`); all other occurrences are struct fields
  (TailZ23,25..29,33..38,41,44) or pass-through `raynaudSemistableSH := n.raynaudSemistableSH`.
- `raynaudSemistableSHOr` (TailZ45 L56) read only at TailZ45 L87 (`raynaudSemistableSH_of_or n.raynaudSemistableSHOr geomConn`).
- readers of raynaudSemistable_of14: raynaudCriterionNF_of14 (TailZ26 L169), semistableReductionDVR_of14 (TailZ23 L727)
  -> ss1_ss3_of14NF (TailZ26 L177); both only in sixContactMin_of_open20 (TailZ26 L186).
- Other theorems taking a research bundle >= 14 on the chain: SGRFold.research14_of_open29 /
  heckeSqrtBranchAny_of_open29 (via openGlue7_of_OpenGlue8, TailZ39), x6Rows/addedLeaves9/researchLeaves9_of_open14.

## Closure probe (VERIFIED, scratch/raynaud-narrow/FieldUse.lean, fielduse-output.txt, 7 min)
closure of ZInQ.OneProof.frozenTarget: 268,667 constants. Constants mentioning a projection `...raynaudSemistableSH`,
`...raynaudSemistableSHOr` or the types ReductGlue.RaynaudSemistableSH / DictModels.RaynaudOr.RaynaudSemistableSHOr:
constructors OpenResearchLeaves14..28.mk, pass-through maps 14_of_15 .. 26_of_27, 27_of_28 (reads SHOr, via
raynaudSemistableSH_of_or), HDec.HSyn.raynaudSemistable_of14, and the lemmas ReductB.raynaudSemistable_of_SH_pair,
ReductGlue.raynaudSemistable_of_SH' (take the leaf as hypothesis). Hence the only semantic reader is
raynaudSemistable_of14 -> {raynaudCriterionNF_of14, semistableReductionDVR_of14 -> ss1_ss3_of14NF} -> open20. Same as
raynaud-proof's finding on TailZ42; confirmed on TailZ45.

## Leaf file (VERIFIED, compiles, standard axioms)
ZInQKernel/Contrib/OneProof/RaynaudSemistableSHcpOr.lean: def RaynaudNarrow.RaynaudSemistableSHcpOr (SHOr + [CharZero K]
+ [PerfectField κ(O)]); cpOr_of_or (SHOr → cpOr), cpOr_of_cp, raynaudSemistableSHcp_of_cpOr (+ GeomConn),
raynaudSemistableSHcp_of_cpOr' (GeomConn discharged by geomConnOfRationalPoint_proof). lake build: success.
