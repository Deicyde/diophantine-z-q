# e1-sub fold notes (leaf-adopt3)

Fragment: `scratch/leaf-adopt3/fold/e1-sub.lean`, section `E1SubSec`, namespace `E1Sub`.
Source: `scratch/e1-sub/E1Sub.lean` lines 20-870, verbatim except for the `hiding` change below.
The import is dropped and the 11 `#print axioms` lines are dropped.

**Order.** The fragment needs glue-ssbc's `GlueSSBCSec` before it. It must come before c9-rhof,
which uses `GlueI3.isSemisimpleRepresentation_baseChange` defined here. It does not use x1-belyi.
The order x1-belyi, e1-sub, c9-rhof is fine.

## Bundle and glue changes
- **Glue target `LeafModCurves.VSurjOfSurjective` (leaf-modcurves; G13's open item) is proved** from
  fields `r9a` (`PkgI3.FaltingsSemisimple`), `r9b` (`PkgI3.FaltingsTate`) and `t26`
  (`PkgI3.TateModuleFree`). No new leaf.
- G13, sub form: `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ`. It is proved from `r16`,
  `r9a`, `r9b`, `t26`. It also gives semisimplicity of `rhoF` (`rhoF_semisimple_of_surj`).
- E1 for R16 (`E1_R16`) is proved from `r16`, `r9a`, `r9b`, `t26` and `t8` (`PkgI3.PoincareReducibility`).
  It is conditional on the `A'`-side isomorphism `U ≃ ρ_{f,ι}|_{G_L}` (C9's output) and on
  `EndDivision A'`.

## Bridging theorems (exact Leaves.lean types)
- `E1Sub.vSurjOfSurjective (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree) : LeafModCurves.VSurjOfSurjective`
  (from the task file, unchanged).
- `E1Sub.g13_constituent'`: `LeafModCurves.g13_constituent` with its hypothesis `VSurjOfSurjective`
  discharged. Hypotheses: `r16`, `r9a`, `r9b`, `t26`.
- `E1Sub.rhoF_subrep_J`, `E1Sub.rhoF_semisimple_of_surj`, `E1Sub.rhoF_subrep_JL`,
  `E1Sub.rhoFL_subrep_JL`, `E1Sub.E1_R16`. All hypotheses are Leaves.lean leaves:
  `LeafModCurves.R16_EichlerShimuraJ1'`, `PkgI3.FaltingsSemisimple`, `PkgI3.FaltingsTate`,
  `PkgI3.TateModuleFree`, `PkgI3.PoincareReducibility`.
- Also: `homVK_surjective` (any number field), `bcVE_injective`, `bcVE_equivariant`, `exists_res`,
  `res`, `bcT_bijective`.
- `#print axioms` dropped: `vSurjOfSurjective`, `homVK_surjective`, `rhoF_subrep_J`, `bcVE_injective`,
  `bcVE_equivariant`, `exists_res`, `rhoF_subrep_JL`, `E1_R16`, `rhoFL_subrep_JL`, `bcT_bijective`,
  `g13_constituent'`.

## Kernel declarations copied in (not in Leaves.lean), placed before use
1. `GlueI3.isSemisimpleRepresentation_baseChange` and `GlueI3.semisimpleBaseChange` (kernel
   `I3Linalg/C2.lean`, glue-ssbc block L270-455).
   - These are not a verbatim copy of the kernel's 11-declaration block. They are wrappers: the first
     is `:= GlueSSBC.isSemisimpleRepresentation_baseChange E ρ hρ`; the second has the kernel's body
     verbatim.
   - They rely on `GlueSSBC.repBaseChange` and `GlueI3.repBaseChange` being defeq. The two have
     identical bodies, so they are equal by unfolding.
   - Fallback if that fails, or if the glue-ssbc fragment already declares these two `GlueI3` names:
     paste kernel `C2.lean` L270-455 verbatim (`GlueI3.TraceNondeg` … `GlueI3.semisimpleBaseChange`),
     or rename.
2. `PkgI3.E1_exists_hom_ne_zero'` (kernel `C2.lean` L804-816), verbatim, inside
   `namespace PkgI3 open GlueI3 AbVar`.
3. Kernel `I3Linalg/TateBC.lean` §2 in full, verbatim: `PkgI3.Tate.map_injective`, `ell_smul_succ`,
   `mem_range_of_ell_smul`, `mem_range_of_pow_smul`, `mem_range_of_smul`, `map_bijective`.
- Not used, so not copied: `PkgI3.C2_absolutelyIrreducible'` and
  `GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four'`. Each is a two-line corollary of
  `GlueI3.semisimpleBaseChange` and could be added for the C2 row.

## Kernel names used that Leaves.lean has with the same text
- `GlueI3`: `projection_comm`, `repBaseChange`, `isSemisimple_of_surjective`, `SemisimpleBaseChange`.
- `PkgI3`: `E1_exists_hom_ne_zero`, `homT_galT`, `Tate.map`/`T`/`smulSeq_congr`, the `AbVar.*` object
  layer (`homT`, `tateHom`, `tateHomZl`, `galT`, `galRep`, `baseChange`, `dim`, `Hom.*`), `EndDivision`,
  `IsIsogenyMor`.
- `LeafModCurves`: `homV`, `homV_galRep`, `VSurjOfSurjective`, `rhoF`, `eigenFun`, `finrank_rhoF`,
  `trace_rhoF`, `dualAct`, `g13_constituent`, `coeffField`, `IsJ1`, `IsFrobAt`,
  `R16_EichlerShimuraJ1'`.
- `PkgI4`: `GQ`, `CF`, `IsNewform`, `coeff`.

## Statement differences and the one textual change
Leaves.lean's `LeafModCurvesSec` declares its own copies of 11 names: `LeafModCurves.Qbar`, `GQ`,
`LiesOver`, `IsArithFrob`, `CF`, `coeff`, `HasNebentypus`, `IsNormalizedEigenform`, `scaleH`,
`oldSpace`, `IsNewform` (L15959-16046). The kernel `ModCurves/Defs.lean` instead does
`open PkgI4 (…)`.

This has two consequences:
1. **Textual change.** In e1-sub, `open LeafModCurves` + `open PkgI4 (GQ)` would make `GQ` ambiguous.
   Both `open LeafModCurves` lines (sections `RhoSub`, `Final`) therefore become
   `open LeafModCurves hiding Qbar GQ … IsNewform`. All these names then resolve to `PkgI4`'s, as in
   the kernel.
2. **No textual change, but a defeq crossing.** In Leaves.lean, `LeafModCurves.R16_EichlerShimuraJ1'`,
   `g13_constituent` and `isFrobAt_of_isArithFrob` are stated over `LeafModCurves.CF/coeff/IsNewform/…`,
   not `PkgI4.*` as in the kernel. e1-sub passes `PkgI4`-typed terms into them (`hf : PkgI4.IsNewform f χ`,
   `ha : (a:ℂ) = PkgI4.coeff f p`). `g13_constituent'` is stated with `PkgI4.coeff` but proved by
   `g13_constituent …`. These checks need delta-unfolding of defs with identical bodies, which should
   succeed. No `rw` crosses the two vocabularies.

## Expected trouble spots
- The `GlueI3` wrappers: the defeq between `GlueSSBC.repBaseChange` and `GlueI3.repBaseChange`, and a
  possible name clash with the glue-ssbc fragment.
- The `PkgI4`/`LeafModCurves` vocabulary unifications listed above (`rhoF_subrep_J`, `g13_constituent'`).
