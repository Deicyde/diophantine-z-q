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
- lake build of the 7 NewForm imports + ZInQKernel.HDecomp.C10.Link: OK (6m51s).
- run1 (`lake env lean scratch/g14-trace/G14Trace.lean`, 38 s): 2 errors in `g7Out_twist`
  (rw under a lambda); everything else compiled.
- run2: exit 0, no error, no `sorry`; 29 `#print axioms` (19 copied + 10 new) all
  `[propext, Classical.choice, Quot.sound]` (VERIFIED).

## Statements (VERIFIED compiled, run2), namespace `G14Trace`
- `g7Out_twist`: `G7Out A ℓ Tm c ε a β u` ⇒ `G7Out A ℓ Tm c ε (χ·a) β u` for continuous
  `χ : G_ℚ →* ℚ̄_ℓ^×` with `χ ∘ resQ K = 1`. `trace_rho_twist`: `tr ρ_{χa} = χ · tr ρ_a`.
- `trace_of_intertwines`: `Intertwines f m e` ⇒ `tr f(g) = 2 tr m(g)`.
- `trace_eq_image`: `N tr T = t`, `tr((jβ)⁻¹ ja • T) = 2 tr m` ⇒ `tr m = j(½ β⁻¹ a t/N)`.
- `FrobTraceLink A Tm₅ Tm₃` (glue Prop, AV side), `FrobSquaresLink` (glue Prop, square form),
  `frobTraceLink_of_squares` (proved).
- `common_trace` (T7 + GalG8Out at 3, 5 on `rho Tm_ℓ (j_ℓ∘a) (j_ℓ∘β)` + FrobTraceLink):
  outside finite `S`, at arithmetic Frobenius, `tr r₅ = j₅ x`, `tr r₃ = j₃ x`.
- `exists_comp_eq`: any two `ℚ`-embeddings `ι, j : ℚ̄ → F` satisfy `ι = j ∘ γ`.
- `g14TraceCompat_of_common`, `g14TraceCompat_of_link`: `G14TraceCompat D` for such data with
  `ι₅ = j₅∘γ`, `ι₃ = j₃∘γ`.
- `g12Spec_g14_of_galois` (+ g0-mod-newform's `DirichletOfFinite`, `GalG12Out r₅`):
  `∃ D, D.r5 = r5 ∧ D.r3 = r3 ∧ G12Spec D ∧ G14TraceCompat D`.
