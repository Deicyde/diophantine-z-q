# prop-ts results log

Base f90cf864 (wip/prop-ts). Object: `G0ModField.PropTS`, `PropTSAll` from
`scratch/fibre-cover/FibreCover.lean`, copied into `scratch/prop-ts/PropTS.lean`;
`check_identical.py`: both IDENTICAL (VERIFIED).

## Step 1 (06:40): leaf + glue + reduction, compiled
- Build: `lake build ZInQKernel.HDecomp.QM.Leaves ZInQKernel.HDecomp.Descent.B2Glue
  ZInQKernel.HDecomp.QM.Pin` OK.
- `lake env lean scratch/prop-ts/PropTS.lean`: 0 errors (VERIFIED, compile_out.txt).
- Defs: `InfCoord` (ℚ[s], s ↦ X⁻¹), `infAlg`, `intPolyAlg`, `vertPrime`, `BranchData`,
  `NoVerticalRam`, `BeckmannSIT` (leaf), `FunctionFieldModel`, `nY3`, `CoverBranchData`,
  `CoverModel`.
- Theorems (axioms [propext, Classical.choice, Quot.sound], VERIFIED):
  `padicValRat_16_27`, `propTS_of_coverModel : BeckmannSIT → CoverModel Y π → PropTS Y π`,
  `propTSAll_of_coverModel`.
