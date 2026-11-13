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

## Step 3 (06:50): Beckmann as glue from purity + T2 (Abhyankar), compiled
- New defs: `NonMeeting`, `SpecNonMeeting` (glue from purity, t-purity3), `KummerStep`,
  `KummerGlue := PkgI2.AbhyankarDVR.{0} → KummerStep`, `UnramifiedMono` (textbook),
  `BeckmannSITTame` (BeckmannSIT + `0 < n_b < p`, `0 < nInf < p`).
- New theorems, standard axioms (VERIFIED): `beckmannSITTame_of`, `beckmannSITTame_of_glue :
  KummerStep → SpecNonMeeting → UnramifiedMono → BeckmannSITTame`, `propTS_of_coverModel_tame`,
  `propTSAll_of_bundle : AbhyankarDVR → R1R2fp → KummerGlue → SpecNonMeeting → UnramifiedMono →
  MobiusGlue → CoverModelOfHecke → PropTSAll`.
- `NonMeeting` requires `f.eval s₀ ≠ 0` explicitly (padicValRat p 0 = 0 would otherwise let a
  vanishing f count as a unit).
