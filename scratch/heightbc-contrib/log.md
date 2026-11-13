# heightbc-contrib results log

- Merged origin/wip/hodge-bc2 (116dc2f2) and origin/main (b7cdba8e): merge commit 285c1e37.

## Step 1: statement check (VERIFIED by reading the files and by verbatim_check.py)

| Prop | where defined (owner) | where proved | kernel / scratch |
|---|---|---|---|
| `ZInQ.H5Neron.ModelHeightBaseChange` (H4a) | ZInQKernel/HDecomp/Faltings/H5Neron.lean:618 | hodge-bc2 (IntegrationBC, over the copy `ZInQ.HeightBC.ModelHeightBaseChange`) | **kernel**; copies in scratch/height-bc/Final.lean:52, scratch/h5-glue/H5Final.lean:1989, scratch/g0-stablebc/Main.part:43 |
| `ZInQ.H5Neron.OpenSubgroupHeight` (M6) | H5Neron.lean:635 | h5-glue `openSubgroupHeight` (over the copy H5Final.lean:1998) | **kernel** |
| `ZInQ.H5Neron.GroupModelBaseChangeExists` (H4b) | H5Neron.lean | kernel `ZInQ.H5Neron.groupModelBaseChangeExists` (H5BaseChange.lean:201) | **kernel** (already proved) |
| `ZInQ.H5Neron.NeronModelExists` (N1), `SemistableNeronIdentityComponent` (N2) | H5Neron.lean:205, :603 | literature leaves (hypotheses) | **kernel**; copies in H5Final.lean:1961, :1974 |
| `ZInQ.DefFaltings.NeronModelMinimal` | ZInQKernel/HDecomp/Faltings/Height.lean:289 | h5-glue `neronModelMinimal` (stated over the kernel def itself) | **kernel** |
| `ZInQ.HeightBC.HodgeBCInjective` | scratch/height-bc/Final.lean:1459 | hodge-bc2 hbc_proof.lean.part | scratch |
| `ZInQ.HeightBC.OmegaBaseChange` | scratch/height-bc/Final.lean:1159 | hodge-bc2 omega_proof.lean.part | scratch |
| `ZInQ.HeightBC.OmegaLocalization` | scratch/hodge-bc2/omega_proof.lean.part | hodge-bc2 omega_proof.lean.part | scratch |
| `ZInQ.HeightBC.CotangentSpanBC` | scratch/height-bc/Final.lean:1752 | infra-stalks bc_proof.lean.part | scratch |
| `ZInQ.HeightBC.UniformizationLiftAnalytic` | scratch/height-bc/Final.lean:1853 | infra-stalks ula_proof.lean.part | scratch |
| `ZInQ.HeightBC.HodgeLineBaseChange` | scratch/height-bc/Final.lean:244 (verbatim from scratch/g0-stablebc/Main.part:414) | hodge-bc2 int_final.lean.part | scratch |
| `G0StableBC.StableHeightBaseChange` (g0-split piece 6) | scratch/g0-split/Split.lean:19491 (copied in g0-stablebc Main.part:14; same body as `G0Split.StableHeightBaseChange`, scratch/h-decomposition/Leaves.lean:33610) | hodge-bc2 int_final.lean.part | scratch (uses the alias `ZInQ.DefFaltings.AbVar := PkgI3.AbVar`, height-bc PartE) |

No kernel file defines `HodgeLineBaseChange`, `StableHeightBaseChange`, `HodgeBCInjective`,
`OmegaBaseChange`, `CotangentSpanBC`, `UniformizationLiftAnalytic` or `OmegaLocalization`
(grep over ZInQKernel/, VERIFIED).

Consequences for the port:
- the Contrib theorems for H4a, M6 and NeronModelMinimal get the kernel's Props as types
  (`ZInQ.Contrib.HeightBC.modelHeightBaseChange : ZInQ.H5Neron.ModelHeightBaseChange`, etc.);
  the copies are linked to the kernel Props by `Iff.rfl` theorems (Lean-level check);
- H5 is restated with the kernel's N1, N2 as hypotheses, through the kernel's
  `ZInQ.H5Neron.stableFaltingsHeight_eq_neron_all`;
- h5-glue's Part 1 (H5Final.lean 20-712, a copy of hodge-lattice §1-§5 into the namespace
  `ZInQ.DefFaltings.HodgeLattice`) duplicates declarations of the kernel's
  ZInQKernel/HDecomp/Faltings/HodgeLattice.lean (`diff`: only 3 re-wrapped lines differ), so it is
  replaced by an import of that kernel module (otherwise any file importing both would fail).
- `scratch/heightbc-contrib/verbatim_check.py`: 24 checks, ALL OK (exact text of the scratch-only
  Props against their owners; bodies of the kernel-Prop copies against H5Neron.lean up to
  whitespace).
