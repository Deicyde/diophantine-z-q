# g14-trace results log

Base: 2dd83306 (wip/integrate-w36b). Target: `G0ModNewform.G14TraceCompat D`
(scratch/g0-mod-newform/part_new.lean L197), on the data `D : ModData L A`.

## Files
- `part_c9_src.lean`, `part_e1_src.lean`, `part_new.lean`: verbatim copies from
  scratch/g0-mod-newform/ (diff against its NewForm.lean: only the two added comment/blank lines).
- `part_g14.lean`: new section (namespace `G14Trace`).
- `build.sh`: assembles `G14Trace.lean` (NewForm's imports + `ZInQKernel.HDecomp.C10.Link`).

## Findings
- F1 (VERIFIED by reading): g0-mod-field's `TateBridge` (ModField.lean L1021) gives, for each `ℓ`
  separately, `∃ Tm c ε' a β' uu, G7Out …`; nothing ties the `ℓ = 3` data to the `ℓ = 5` data or to
  `G7Data`'s `β`. Its docstring says the scalars are "mapped into ℚ̄_ℓ by one embedding of the
  number field they generate", but the formal statement drops it.
- F2 (Lean, `g7Out_twist`, `trace_rho_twist`): `G7Out` at one `ℓ` is preserved by `a ↦ χ·a` for a
  continuous `χ : G_ℚ → ℚ̄_ℓ^×` trivial on `G_K`, and `tr ρ` is multiplied by `χ`. So
  `G14TraceCompat` is not a consequence of `G7Out` at 3 and 5 separately.
- F3 (VERIFIED by reading): the kernel already has the trace link (ZInQKernel/HDecomp/C10/Link.lean:
  `FrobCompare`, `trace_T_of_frobCompare`, `FrobSquares`, `frobCompare_of_frobSquares`), over the
  same `PkgI3.AbVar`, `GlueDescent.rho`, and the leaf `PkgI3.CharPolyIndepOfEll` (T7).

## Compile outcomes
