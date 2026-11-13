# heightbc-contrib: the height base-change chain in the kernel's Contrib build (2026-11-13)

## Main result

The closed height base-change chain (tasks height-bc, infra-stalks, hodge-bc2, g0-stablebc,
h5-glue) now lives in 16 new modules under `ZInQKernel/Contrib/HeightBC/`. Every module builds
with `lake build`. No existing file was changed.

The kernel's glue H4a, glue M6 and `NeronModelMinimal` are now Contrib theorems whose types are
the kernel's own Props. H5 follows from the kernel's two literature leaves N1 and N2 alone.
All results below are VERIFIED (built, no `sorry`):

```lean
-- ZInQKernel/Contrib/HeightBC/Main.lean, namespace ZInQ.Contrib.HeightBC
theorem modelHeightBaseChange : ZInQ.H5Neron.ModelHeightBaseChange          -- glue H4a
theorem openSubgroupHeight : ZInQ.H5Neron.OpenSubgroupHeight                -- glue M6
theorem neronModelMinimal : ZInQ.DefFaltings.NeronModelMinimal
theorem stableFaltingsHeight_eq_neron_of_N1N2 (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hN2 : ZInQ.H5Neron.SemistableNeronIdentityComponent)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀)
      (𝒩₀ : DefFaltings.GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ DefFaltings.stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : DefFaltings.GroupModel A L'), 𝒩'.IsNeronModel →
        DefFaltings.stableFaltingsHeight A = 𝒩'.height
```

How `stableFaltingsHeight_eq_neron_of_N1N2` is proved:
- it is the kernel's `ZInQ.H5Neron.stableFaltingsHeight_eq_neron_all`;
- three of that theorem's four glue hypotheses are discharged by the three theorems above;
- the fourth, `GroupModelBaseChangeExists`, by the kernel's `ZInQ.H5Neron.groupModelBaseChangeExists`.

The scratch-only Props of the chain are also theorems. Their statements are verbatim copies of
the owners' text:

```lean
theorem ZInQ.HeightBC.hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective             -- HodgeBCInjective.lean
theorem ZInQ.HeightBC.omegaLocalization : ZInQ.HeightBC.OmegaLocalization           -- OmegaBC.lean
theorem ZInQ.HeightBC.omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange               -- OmegaBC.lean
theorem ZInQ.HeightBC.cotangentSpanBC : ZInQ.HeightBC.CotangentSpanBC               -- CotangentSpan.lean
theorem ZInQ.HeightBC.uniformizationLiftAnalytic : ZInQ.HeightBC.UniformizationLiftAnalytic
theorem ZInQ.HeightBC.modelHeightBaseChange : ZInQ.HeightBC.ModelHeightBaseChange   -- Main.lean
theorem ZInQ.HeightBC.hodgeLineBaseChange : ZInQ.HeightBC.HodgeLineBaseChange       -- Main.lean
theorem ZInQ.HeightBC.stableHeightBaseChange : G0StableBC.StableHeightBaseChange    -- Main.lean
theorem ZInQ.H5Glue.neronModelMinimal : NeronModelMinimal                           -- H5GlueMinimal.lean
theorem ZInQ.H5Glue.openSubgroupHeight : ZInQ.H5Glue.OpenSubgroupHeight             -- H5GlueOpen.lean
```

`ZInQ.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2` (hodge-bc2's version, with h5-glue's copies
of N1 and N2 as hypotheses) is also ported. The full texts of these Props are in
`docs/research/hodge-bc2.md`, in the `Copies`, `Natural` and `GlueC` modules, and in `G0StableBC`.
`G0StableBC.StableHeightBaseChange` is g0-split's piece 6:

```lean
def StableHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K),
    stableFaltingsHeight (A.baseChange L) = stableFaltingsHeight A
```

Here `ZInQ.DefFaltings.AbVar` is height-bc's alias `abbrev … := PkgI3.AbVar K`, also ported.

`#print axioms` output of `scratch/heightbc-contrib/Check.lean`, in `Check.out`. The 13
contrib-check lines are omitted here; all of them are standard too.

```
'ZInQ.HeightBC.hodgeBCInjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.omegaBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.omegaLocalization' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.cotangentSpanBC' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.uniformizationLiftAnalytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.modelHeightBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.hodgeLineBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.stableHeightBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.H5Glue.neronModelMinimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.H5Glue.openSubgroupHeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.HeightBC.modelHeightBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.HeightBC.openSubgroupHeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.HeightBC.neronModelMinimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The axiom audit `scratch/heightbc-contrib/AxiomAudit.lean` covers all 565 declarations of the
modules `ZInQKernel.Contrib.HeightBC.*` (457 of them theorems). Every one depends only on
`propext`, `Classical.choice` and `Quot.sound`.

Nothing in the chain remains open. No statement change is proposed.

## Step 1: statement check

| Prop | where defined | where proved | kernel / scratch |
|---|---|---|---|
| `ModelHeightBaseChange` (H4a) | `ZInQKernel/HDecomp/Faltings/H5Neron.lean:618` (`ZInQ.H5Neron`) | `Contrib/HeightBC/Main.lean` (from hodge-bc2, over height-bc's copy) | **kernel** |
| `OpenSubgroupHeight` (M6) | `H5Neron.lean:635` | `Main.lean` (from h5-glue's `openSubgroupHeight`, over its copy) | **kernel** |
| `NeronModelMinimal` | `ZInQKernel/HDecomp/Faltings/Height.lean:289` (`ZInQ.DefFaltings`) | `Main.lean` / `H5GlueMinimal.lean` (h5-glue) | **kernel** |
| `GroupModelBaseChangeExists` (H4b) | `H5Neron.lean` | kernel `H5BaseChange.lean:201` (already proved) | **kernel** |
| `NeronModelExists` (N1), `SemistableNeronIdentityComponent` (N2) | `H5Neron.lean:205`, `:603` | literature leaves (hypotheses) | **kernel** |
| `HodgeBCInjective` | `scratch/height-bc/Final.lean:1459` | `HodgeBCInjective.lean` (hodge-bc2) | scratch |
| `OmegaBaseChange` | `scratch/height-bc/Final.lean:1159` | `OmegaBC.lean` (hodge-bc2) | scratch |
| `OmegaLocalization` | `scratch/hodge-bc2/omega_proof.lean.part` | `OmegaBC.lean` (hodge-bc2) | scratch |
| `CotangentSpanBC` | `scratch/height-bc/Final.lean:1752` | `CotangentSpan.lean` (infra-stalks) | scratch |
| `UniformizationLiftAnalytic` | `scratch/height-bc/Final.lean:1853` | `UniformizationLift.lean` (infra-stalks) | scratch |
| `HodgeLineBaseChange` | `scratch/height-bc/Final.lean:244`, verbatim from `scratch/g0-stablebc/Main.part:414` | `Main.lean` (hodge-bc2) | scratch |
| `StableHeightBaseChange` (g0-split piece 6) | `scratch/g0-split/Split.lean:19491`; the same text is at `scratch/g0-stablebc/Main.part:14`, and the same body at `scratch/h-decomposition/Leaves.lean:33610` | `Main.lean` (hodge-bc2) | scratch |

No kernel file defines any of the scratch-only Props (grep over `ZInQKernel/`, VERIFIED).

The copies are checked mechanically in two ways:
- **Text** (`scratch/heightbc-contrib/verbatim_check.py`, 24 checks, `ALL OK`):
  - each scratch-only Prop's docstring and def in the Contrib modules equals its owner's text
    character for character;
  - the bodies of the copies of kernel Props equal `H5Neron.lean`'s bodies up to whitespace. The
    copies checked are height-bc's, h5-glue's and g0-stablebc's `ModelHeightBaseChange` and
    `IsBaseChangeOf`, and h5-glue's N1, N2, M6, H4b and `IsOpenSubgroupModel`.
- **Lean** (`Main.lean`, Part 5): each copy is proved equal to the kernel Prop by `Iff.rfl`. These
  are `heightBC_modelHeightBaseChange_iff`, `h5Glue_modelHeightBaseChange_iff`,
  `g0StableBC_modelHeightBaseChange_iff`, `h5Glue_openSubgroupHeight_iff`,
  `h5Glue_groupModelBaseChangeExists_iff`, `h5Glue_neronModelExists_iff` and
  `h5Glue_semistableNeronIdentityComponent_iff`.

## Step 2: the modules

`scratch/heightbc-contrib/build_modules.py` generates every module from the scratch sources, and
its assertions pin the cut points. Each module consists of four parts:
- a header;
- at most a few context lines;
- a VERBATIM slice, with `#print` lines dropped;
- at most a closing `end`.

The slices are exactly the pieces that `scratch/hodge-bc2/assemble_h5.py` concatenates into
`IntegrationH5.lean`. In dependency order:

| module | source |
|---|---|
| `StalkPullback` | infra-stalks `StalkPullback.lean` (Mathlib-only) |
| `LocalStructure` | infra-stalks `local_structure.lean.part` (Mathlib-only) |
| `StalkTensor` | infra-stalks `stalk_tensor.lean.part` (Mathlib-only) |
| `CotangentBC` | infra-stalks `cot_bc.lean.part` (Mathlib-only) |
| `Copies` | height-bc `Final.lean` lines 3-589 (copies, Part A) |
| `Natural` | `Final.lean` lines 591-1443 (Part B) |
| `GlueC` | `Final.lean` lines 1445-2101 (Part C) |
| `CotangentSpan` | infra-stalks `bc_proof.lean.part` |
| `UniformizationLift` | infra-stalks `ula_proof.lean.part` |
| `HodgeBCInjective` | hodge-bc2 `hbc_proof.lean.part`; imports `Contrib/HodgeBC2/ExtFrac.lean` as it is |
| `OmegaBC` | hodge-bc2 `omega_proof.lean.part` |
| `G0StableBC` | height-bc `PartE.lean.part` alias, then g0-stablebc `Main.part` |
| `H5GlueMinimal` | h5-glue `H5Final.lean` lines 714-1731 (Part 2) |
| `H5GlueReduction` | `H5Final.lean` lines 1732-2358 (Part 3) |
| `H5GlueOpen` | `H5Final.lean` lines 2359-2627 (Part 4) |
| `Main` | infra-stalks `hbc_final`, PartE tail, hodge-bc2 `int_final`, `int_h5`, and the new Part 5 |

**One deviation from IntegrationH5: h5-glue's Part 1 is replaced by a kernel import.**
- h5-glue's Part 1 (H5Final.lean lines 20-712) is a copy of hodge-lattice §1-§5 in the namespace
  `ZInQ.DefFaltings.HodgeLattice`.
- That text is already in the kernel as `ZInQKernel/HDecomp/Faltings/HodgeLattice.lean`.
  `diff` shows only three re-wrapped lines.
- A file that imports both copies would fail on the duplicate declarations, and
  `Contrib/AbVarBC/Consumers.lean` already imports the kernel module.
- So `H5GlueMinimal` imports the kernel module instead of copying Part 1.

**Build.** Every module was built with `lake build ZInQKernel.Contrib.HeightBC.<M>`, one at a time in
dependency order (VERIFIED). Each took 8-20 s once its dependencies were built. No error, no
`sorry`, and no proof needed any change.

## Step 3: Check.lean

`scratch/heightbc-contrib/Check.lean` is `scratch/contrib-check/Check.lean` plus three additions:
- `import ZInQKernel.Contrib.HeightBC.Main`;
- ten `example`s, each stating a closed theorem at its Prop;
- fifteen `#print axioms` lines.

Result of `lake env lean`: 0 errors in 12 s, and all 28 axiom lines are standard (VERIFIED,
`Check.out`). This also shows that the HeightBC modules coexist with HeckeAll, GaussFE, PSide,
GZDecomp, T14, T28, RLeaf and AbVarBC with no duplicate names.

## Remarks

- **Licence.** No Tau Ceti code was vendored. `diffcheck2.py` reports MOD-UNNOTED 0 and
  NOTE-ONLY 0.
- **Namespaces are unchanged.** All namespaces are kept as in the scratch sources (`ZInQ.HeightBC`,
  `ZInQ.H5Glue`, `G0StableBC`, `AlgebraicGeometry` for the Mathlib-only lemmas, `ZInQ.HodgeBC2`).
  The new theorems are in `ZInQ.Contrib.HeightBC`.
- **Possible clash.** The alias `ZInQ.DefFaltings.AbVar` (from height-bc's PartE) would clash
  with any later Contrib module that declares the same name.
- **Locators.** The literature locators in the copied docstrings (EGA, SGA 7, BLR, Faltings) are
  UNVERIFIED. All Lean claims are VERIFIED.
