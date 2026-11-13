# heightbc-contrib (2026-11-13)

**Main result.** The closed height base-change chain is now in the kernel's Contrib build:
16 new modules under `ZInQKernel/Contrib/HeightBC/`, generated verbatim from the scratch sources
by `scratch/heightbc-contrib/build_modules.py`. The kernel's glue H4a and M6 and its
`NeronModelMinimal` are theorems whose types are the kernel's own Props. H5 follows from the
kernel's leaves N1 and N2 alone:

- `ZInQ.Contrib.HeightBC.modelHeightBaseChange : ZInQ.H5Neron.ModelHeightBaseChange`
- `ZInQ.Contrib.HeightBC.openSubgroupHeight : ZInQ.H5Neron.OpenSubgroupHeight`
- `ZInQ.Contrib.HeightBC.neronModelMinimal : ZInQ.DefFaltings.NeronModelMinimal`
- `ZInQ.Contrib.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2 (hN1 : ZInQ.H5Neron.NeronModelExists) (hN2 : ZInQ.H5Neron.SemistableNeronIdentityComponent) K A : ∃ L₀ … 𝒩₀, 𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧ ∀ L' 𝒩', 𝒩'.IsNeronModel → stableFaltingsHeight A = 𝒩'.height`

The scratch-only Props are theorems too, with verbatim statements:
`ZInQ.HeightBC.{hodgeBCInjective, omegaLocalization, omegaBaseChange, cotangentSpanBC,
uniformizationLiftAnalytic, modelHeightBaseChange, hodgeLineBaseChange, stableHeightBaseChange
(: G0StableBC.StableHeightBaseChange), stableFaltingsHeight_eq_neron_of_N1N2}` and
`ZInQ.H5Glue.{neronModelMinimal, openSubgroupHeight}`.

**What compiles.**
- Every module builds with `lake build`.
- The axiom audit (`AxiomAudit.lean`) covers all 565 HeightBC declarations: each depends only on
  propext, Classical.choice and Quot.sound.
- `scratch/heightbc-contrib/Check.lean` (contrib-check plus HeightBC) runs with 0 errors, and all
  28 `#print axioms` lines are standard.

**Statement check.**
- `verbatim_check.py` reports ALL OK on 24 text checks.
- `Iff.rfl` theorems in Main.lean prove that each copy equals the kernel's Prop (H4a, M6, H4b, N1, N2).
- The table is in `docs/research/heightbc-contrib.md`.

**One deviation.** h5-glue's Part 1 duplicated the kernel's `HDecomp/Faltings/HodgeLattice.lean`.
It is replaced by an import of that module, so no name is declared twice.

**What remains.** Nothing in this chain. No statement changes are proposed.
