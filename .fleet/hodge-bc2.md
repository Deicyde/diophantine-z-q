# hodge-bc2 (2026-11-13)

**Main result.** Both of height-bc's remaining glue Props are now Lean theorems, with their
statements copied verbatim:
- `ZInQ.HeightBC.hodgeBCInjective : HodgeBCInjective`
- `ZInQ.HeightBC.omegaBaseChange : OmegaBaseChange`, via the new named Prop `OmegaLocalization`,
  which is also proved (`omegaLocalization`).

Together with infra-stalks' `cotangentSpanBC` and `uniformizationLiftAnalytic`, three more targets
become theorems with no hypotheses:
- **H4a** `modelHeightBaseChange : ModelHeightBaseChange`;
- `hodgeLineBaseChange : HodgeLineBaseChange`;
- g0-split's piece 6, `stableHeightBaseChange : G0StableBC.StableHeightBaseChange`.

h5-glue's H5 (multi-field form) now needs only the literature leaves N1 and N2
(`stableFaltingsHeight_eq_neron_of_N1N2`). Every theorem above depends only on the axioms
`[propext, Classical.choice, Quot.sound]`.

**What compiles.** Each check is a single file, run with `lake env lean`, with 0 errors and no
`sorry`:
- `scratch/hodge-bc2/HodgeBCInjective.lean` (21 s)
- `scratch/hodge-bc2/OmegaBC.lean` (21 s)
- `scratch/hodge-bc2/IntegrationBC.lean` (26 s; infra-stalks' `HeightBCGlue.lean` plus g0-stablebc's
  `Main.part`, both verbatim)
- `scratch/hodge-bc2/IntegrationH5.lean` (40 s; plus h5-glue's `H5Final.lean`, verbatim)

The scripts `assemble.py`, `assemble_int.py` and `assemble_h5.py` regenerate these files, and
`verbatim_check.py` prints ALL OK. The new Mathlib-only module `ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean`
(`K ⊗_R ⋀_R M ≅ ⋀_K M`, with a basis) builds with `lake build`.

**Proof ideas.**
- `HodgeBCInjective`:
  - The cotangent space gets an `L`-structure through the function field.
  - `π^*` sends an `L`-basis to an `L'`-basis: injectivity comes from infra-stalks'
    `cotangent_baseChange_injective` plus flatness, spanning from `cotangentSpanBC`.
  - `ψ` sends the basis `1 ⊗ ιMulti_family b` (`extFracBasis`) of one Hodge space onto the
    corresponding basis of the other.
- `OmegaBaseChange`:
  - local–global over `𝓞_{L'}`;
  - conormal base change at each point, from `pullback_stalkGen`;
  - `OmegaLocalization`: germ extension, finitely many bad closed points, and a saturation argument
    through the DVR `R_𝔭`.

**What remains.** Nothing in this group. No statement changes are proposed.

**Report:** `docs/research/hodge-bc2.md`. **Log:** `scratch/hodge-bc2/log.md`.
