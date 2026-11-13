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

## Step 2 (06:45): pin route + leaf (a) weakened to `[E : ℚ(X)] < p`
- `BeckmannSIT` hypothesis (a) is now `Module.finrank (RatFunc ℚ) E < p` (weaker than `p ∤ |G|`,
  so the leaf is implied by any version of Beckmann's theorem).
- New, compiled, standard axioms (VERIFIED): `residueImage_comp_eq_of_pt` (Φ' = Φ ∘ g ⇒
  ℚ(g∘y') = ℚ(y')), `propTS_transfer` (along kernel `Pin.SameTripleMor`),
  `propTSAll_of_witness` (kernel `MobiusGlue` + `R1R2fp` + PropTS on one triple),
  `propTSAll_of_leaves : BeckmannSIT → R1R2fp → MobiusGlue → CoverModelOfHecke → PropTSAll`.
- Copied with proofs from fibre-cover: `spec_to_specQ_eq`, `exists_factor_of_residueImage_le`,
  `residueImage_le_aux`, `residueImage_comp_le_self_aux`.
- Sanity: `example (h : BeckmannSIT) := h (RatFunc ℚ)` elaborates (instances satisfiable).
