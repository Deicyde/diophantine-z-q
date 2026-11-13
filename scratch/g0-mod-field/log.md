# g0-mod-field results log

## Setup
- Base 883c4ddf + merge of origin/wip/g0-split (for scratch/g0-split/Split.lean, ModularConstituent).
- Built once: `lake build ZInQKernel.HDecomp.QM.Leaves` (2 min), `lake build ZInQKernel.Hypotheses.JHeight`
  (builds upstream lean/ helpers; needed for any import that reaches `ZInQ.*`).
- `ZInQKernel.Main` cannot be imported from scratch in this tree; `le_heightD_of_mem_S_mul` copied.

## run1-5 (02:00): scratch/g0-mod-field/ModField.lean
- Statements: `FibreCtx`, `IsModelOver`, `G2Out`, `DescentDatum`, `G4Out`, `G7Out`, `FibreCoverOut`,
  `KernelFieldOut`, `FibreCoverExists`, `KernelFieldExists`.
- Proved: `baseChangeTrans`, `isModelOver_baseChange`, `admissible_S_mul`, `g7Out_of_g4Out`,
  `g2Out_of_cover`, `g4Out_of_kernelField`, `fieldDescent`.
- VERIFIED: `lake env lean scratch/g0-mod-field/ModField.lean`: 0 errors, no sorry;
  `#print axioms fieldDescent`, `g7Out_of_g4Out`: [propext, Classical.choice, Quot.sound].

## run6-9 (02:05): twist and unramifiedness of L'
- Built `ZInQKernel.HDecomp.B3Unram.T32a` (oleans absent before).
- New: `b3_of_cochain` (glue-descent's B3 proof with B2's cochain as hypotheses), `two_mem_T`,
  `G7Data` (clause list), `G7OutUnr`, `g7OutUnr_of_g4Out` (B2 + `GlueB3Unram.unramified_outside_noLeaf`
  + B3 + `degree_le_QM`), `g7Out_of_g7OutUnr`.
- Pitfall: `open MonObj` makes `η` a token; binder names `η` fail to parse.
- VERIFIED: 0 errors; `#print axioms g7OutUnr_of_g4Out`: [propext, Classical.choice, Quot.sound].
