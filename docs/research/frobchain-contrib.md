# frobchain-contrib: the frob chain in the kernel's Contrib build (2026-11-13)

Task frobchain-contrib. Lean: `ZInQKernel/Contrib/FrobChain/` (10 new modules). Scripts, checks and
log: `scratch/frobchain-contrib/` (`build_modules.py`, `verbatim_check.py`, `Check.lean`,
`AxiomAudit.lean`, `log.md`).

Marks: **VERIFIED** = compiled or read in a file here. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. This is model work; no human has reviewed it.

## Main result

The closed frob chain now lives in the kernel's Contrib build. The chain consists of:
- frob-trace;
- mul-rigidity;
- alg-frob-red;
- afr-absfrob, through frob-contrib's adoption `Contrib/AbsFrob/`;
- frob-pieces;
- linked-frob.

Every module builds with `lake build`, and no existing file was changed. Three glue statements are
Contrib theorems with the owners' Props as their types. All three rest on the same four inputs:
N1-g1, Zariski's connectedness theorem, I2-Red and I2-NMP. `TateBridge35` also needs I3.M0.
All of the following is VERIFIED (built, no `sorry`):

```lean
-- ZInQKernel/Contrib/FrobChain/Main.lean, namespace ZInQ.Contrib.FrobChain
theorem algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed
theorem tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35
theorem linkedFrob_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob
-- the copies (§1)
theorem frobTraceLink_copy_iff {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (G0ModField.GaloisCopy.Vb A 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (G0ModField.GaloisCopy.Vb A 3)) :
    G14Bridge.FrobTraceLink A Tm5 Tm3 ↔ G14Trace.FrobTraceLink A Tm5 Tm3          -- Iff.rfl
theorem smoothGeomConnIntegral_copy_iff :
    AlgFrobRedRed.SmoothGeomConnIntegral ↔ FrobPieces.SmoothGeomConnIntegral       -- Iff.rfl
theorem kernel_leaves_iff :
    (_root_.ObjBridge.ReductionTorsionBijective ↔ PkgI2.ReductionTorsionBijective.{0}) ∧
    (_root_.ObjBridge.NeronMappingAbelianScheme ↔ PkgI2.NeronMappingAbelianScheme.{0}) -- Iff.rfl
```

The owners' theorems, under their own names, are compiled in the same modules:
- frob-pieces: `FrobPiecesGood.algFrobRed_of_neron_nmp` and `tateBridge35_of_neron_nmp`;
- linked-frob: `LinkedFrobRed.linkedFrob_of_neron_nmp`, `linkedFrob_of_algFrobLink`,
  `linkedFrob_of_algFrobRed`, `linkedFrob_of_gen` and `linkedFrob_of_goodRed_nmp`;
- frob-trace: `FrobTrace.tateBridge35_of_algFrobRed`, `algFrobOne_of_red`, `algFrobLink_of_one` and
  `tateBridge35_of_algFrobLink`;
- alg-frob-red and afr-absfrob: `AlgFrobRedRed.algFrobRed_of_gen`, `fExtendGen_of_nmp` and
  `algFrobRed_of_nmp`;
- mul-rigidity: `G0FibreSimple.rigidityHom : G0FibreSimple.RigidityHom`;
- unram-tate: `UnramTate.tateBridge_of_tateModuleFree`;
- g14-trace: `G14Bridge.tateBridge_five_three_of_35`.

The statements of `AlgFrobRed`, `TateBridge35` and `LinkedFrob` are given in the reports
`docs/research/frob-trace.md` §2 and `docs/research/linked-frob.md` §1. The Lean texts are in
`Contrib/FrobChain/FrobTrace.lean:241`, `Bridge35.lean:60` and `LinkedStatement.lean:85`.

`#print axioms` output from `scratch/frobchain-contrib/Check.lean`, saved in `Check.out`. The file
is a copy of `scratch/contrib-check/Check.lean` plus `import ZInQKernel.Contrib.FrobChain.Main`. It
compiles with exit 0 in 7 s. All 48 reports are `[propext, Classical.choice, Quot.sound]`. The 16
contrib-check lines are omitted below; they are standard too.

```
'ZInQ.Contrib.FrobChain.algFrobRed_of_neron_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.FrobChain.tateBridge35_of_neron_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.FrobChain.linkedFrob_of_neron_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.FrobChain.frobTraceLink_copy_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.FrobChain.smoothGeomConnIntegral_copy_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.FrobChain.kernel_leaves_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobPiecesGood.algFrobRed_of_neron_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobPiecesGood.tateBridge35_of_neron_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_neron_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_algFrobLink' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_algFrobRed' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'LinkedFrobRed.linkedFrob_of_goodRed_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobTrace.tateBridge35_of_algFrobRed' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobTrace.algFrobOne_of_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobTrace.algFrobLink_of_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobTrace.tateBridge35_of_algFrobLink' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgFrobRedRed.algFrobRed_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgFrobRedRed.fExtendGen_of_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgFrobRedRed.algFrobRed_of_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgFrobRedRed.absFrob' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobPiecesGood.smoothGeomConnIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobPiecesNeron.goodRedCofinite_of_neron' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobPiecesGood.algFrobRed_of_spread_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrobPiecesGood.tateBridge35_of_spread_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0FibreSimple.rigidityHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'UnramTate.tateBridge_of_tateModuleFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'G14Bridge.tateBridge_five_three_of_35' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Check.lean` also has `#check`s, so the statements are seen to elaborate with no auto-bound
arguments. The output (VERIFIED) shows:
- `FrobTrace.AlgFrobRed : Prop`, `G14Bridge.TateBridge35 : Prop` and `UnramTate.LinkedFrob : Prop`;
- the same for `FrobPiecesNeron.AbVarSpreadsOut` and `FrobPiecesNeron.ProperSmoothGenConnected`;
- `@G14Trace.FrobTraceLink : {K : Type} → [Field K] → [NumberField K] → (A : PkgI3.AbVar K) →
  (PkgI4.GQ → Module.End (PadicAlgCl 5) (G0ModField.GaloisCopy.Vb A 5)) → (PkgI4.GQ → …) → Prop`.

The axiom audit `scratch/frobchain-contrib/AxiomAudit.lean` covers all 572 declarations of the
modules `ZInQKernel.Contrib.FrobChain.*`, 464 of them theorems. Every one depends only on
`propext`, `Classical.choice` and `Quot.sound` (VERIFIED: `AxiomAudit.out`).

**What remains open in the chain.** The open inputs are the hypotheses of the three theorems:
- `FrobPiecesNeron.AbVarSpreadsOut`: neron-lg's glue N1-g1, a scratch Prop.
- `FrobPiecesNeron.ProperSmoothGenConnected`: frob-pieces' leaf candidate, a scratch Prop.
- The kernel leaves I2-Red and I2-NMP (T4 and T3).
- I3.M0 `PkgI3.TateModuleFree`, needed only for `TateBridge35`.

The brief says the textbook leaves T1-T32 are proved. Even so, I found no theorem whose type is
`PkgI2.ReductionTorsionBijective`, `PkgI2.NeronMappingAbelianScheme` or `PkgI3.TateModuleFree`
anywhere in the worktree (grep over `ZInQKernel/` and `scratch/`, VERIFIED). The table in
`docs/research/h-decomposition.md` (lines 1037-1038) lists T3 and T4 as "open". So these three
stay hypotheses here. They are the kernel's own definitions, so once they are proved they plug in
directly. No statement change is proposed.

## 1. Step 1: statement check

| Prop | owner's text | where it is now | kernel / scratch |
|---|---|---|---|
| `G14Bridge.TateBridge35` | `scratch/g14-trace/part_bridge.lean:44` | `FrobChain/Bridge35.lean:60` | scratch |
| `G14Bridge.FrobTraceLink` | `part_bridge.lean:27` (g14-trace's own copy of `G14Trace.FrobTraceLink`, over `GaloisCopy.Vb`) | `Bridge35.lean:43` | scratch |
| `G14Trace.FrobTraceLink` | `scratch/g14-trace/part_g14.lean:156` | `FrobChain/LinkedStatement.lean:43` | scratch |
| `FrobTrace.AlgFrobRed`, `AlgFrobOne`, `AlgFrobLink` | `scratch/frob-trace/part_frob.lean:226, 113, 71` | `FrobChain/FrobTrace.lean:241, 128, 86` | scratch |
| `AlgFrobRedRed.GoodRedCofinite`, `SmoothGeomConnIntegral`, `FExtendGen` | `scratch/alg-frob-red/part_red.lean:101, 178, 1299` | `FrobChain/AlgFrobRed.lean:121, 198, 1319` | scratch |
| `AlgFrobRedRed.AbsFrob` | `part_red.lean:1368` | `Contrib/AbsFrob/AlgFrobRed.lean:21` (frob-contrib, proved there as `absFrob`), imported | scratch (Contrib) |
| `FrobPieces.SmoothGeomConnIntegral` | `Contrib/FrobPieces/SmoothGeomConnIntegral.lean:29` | imported | Contrib |
| `FrobPiecesNeron.AbVarSpreadsOut` (N1-g1) | copy of `ZInQ.NeronLG.AbVarSpreadsOut`, `scratch/neron-lg/NeronLG.lean:468`; checked by frob-pieces' `py/verbatim_check.py` | `FrobChain/Pieces.lean:166` | scratch |
| `FrobPiecesNeron.ProperSmoothGenConnected` | `scratch/frob-pieces/part_neron.lean:52` | `Pieces.lean:181` | scratch |
| `FrobPiecesGood.AbSchemeSpreadsOut` | `part_good.lean:26` | `Pieces.lean:44` | scratch |
| `G0FibreSimple.RigidityHom` | `scratch/mul-rigidity/Rigidity.lean:195` (mul-rigidity's verbatim copy of g0-fibresimple's) | `FrobChain/Rigidity.lean:206` | scratch |
| `UnramTate.LinkedFrob` (and the `def tmOf` it uses) | `scratch/linked-tate/parts/97_linkeddata.lean:201` (`tmOf` :128) | `LinkedStatement.lean:85` (`tmOf` :69) | scratch |
| `G0ModField.G7Data`, `FibreCtx`, `TateBridge` | `scratch/unram-tate/TateBridge.lean` (= g0-mod-field's `ModField.lean` L1-1036 + unram-tate) | `FrobChain/TateBridge.lean` | scratch |
| `PkgI2.ReductionTorsionBijective` (I2-Red, T4) | `ZInQKernel/HDecomp/Objects.lean:975` | used directly | **kernel** |
| `PkgI2.NeronMappingAbelianScheme` (I2-NMP, T3) | `Objects.lean:937` | used directly | **kernel** |
| `PkgI3.TateModuleFree` (I3.M0) | `Objects.lean:437` | used directly | **kernel** |
| `GlueC10Link.FrobCompare` (a definition used inside the statements) | `ZInQKernel/HDecomp/C10/Link.lean:159` | used directly | **kernel** |

Findings (VERIFIED):
- **No kernel file defines any of the chain's glue Props.** I grepped `ZInQKernel/` for the 86
  `def`/`structure`/`abbrev` names of the chain's sources. The only name hits were in other
  namespaces: `jO`, `PtA`, `Vb` (in `ZInQ.Contrib.G9.G0Galois`). The other hits are the two Contrib
  files listed in the table.
- **The kernel Props in the chain are used directly, never through copies.** These are I2-Red,
  I2-NMP, I3.M0 and `FrobCompare`. frob-trace, alg-frob-red, afr-absfrob and frob-pieces were
  written over `import ZInQKernel.HDecomp.*`, and the modules here import the same kernel modules.
  So the theorems' hypotheses are the kernel's Props themselves. `kernel_leaves_iff` also records
  that the kernel's object-bridge forms (`ObjBridge.*`, `Objects.lean:1454, 1467`) agree by
  `Iff.rfl`.
- **Two statements exist as two copies in the chain, and each pair is proved equal by `Iff.rfl`:**
  - `G14Bridge.FrobTraceLink` = `G14Trace.FrobTraceLink` (`frobTraceLink_copy_iff`);
  - `AlgFrobRedRed.SmoothGeomConnIntegral` = `FrobPieces.SmoothGeomConnIntegral`
    (`smoothGeomConnIntegral_copy_iff`).
- **`LinkedFrob` changes environment.** linked-tate compiled `LinkedFrob` over
  `scratch/h-decomposition/Leaves.lean`, which holds in-file copies of the kernel's definitions.
  Here the same text is compiled over the kernel and over `TateBridge.lean`, the environment
  frob-trace's files already use. linked-frob observed that the two environments cannot be imported
  together. All chain files compile unchanged in both (`docs/research/linked-frob.md` §3), and here
  `LinkedFrob`'s text compiles unchanged too. The `UnramTate.LinkedFrob` in this build is therefore
  the owner's text read over the kernel's definitions, which is the form the kernel build can
  consume. I did not check whether Leaves.lean's copies agree with the kernel definitionally,
  because the two cannot be imported together.

## 2. Step 2: the modules

`scratch/frobchain-contrib/build_modules.py` generates modules 1-9 from the scratch sources, and
its assertions pin the cut points and the source identities. Each module has four parts:
- a header (imports and a provenance docstring);
- at most a few context lines;
- VERBATIM slices, with `#print` lines dropped;
- at most a few closing `end` lines.

The order of the slices is that of linked-frob's `assemble.sh`, which is also the order of
frob-pieces' `FrobPiecesFull.lean`. `Main.lean` is new code.

| module | source (all VERBATIM) | context / changes |
|---|---|---|
| `TateBridge` | `scratch/unram-tate/TateBridge.lean` after its 16 imports | imports: its 16 + `ZInQKernel.HDecomp.C10.Link` (frob-trace's) |
| `Bridge35` | `scratch/g14-trace/part_bridge.lean` | the two file-level `open` lines of g0-mod-field's `ModField.lean` |
| `FrobTrace` | `scratch/frob-trace/part_frob.lean` | ModField opens |
| `Rigidity` | `scratch/mul-rigidity/Rigidity.lean` (its own 4 imports) | none |
| `AlgFrobRed` | `scratch/alg-frob-red/part_red.lean` minus lines 1363-1373 | ModField opens. The deleted block (docstring + `def AbsFrob`) is character-for-character in frob-contrib's `Contrib/AbsFrob/AlgFrobRed.lean`, which is imported |
| `FExtend` | `scratch/afr-absfrob/part_fext.lean` | ModField opens. afr-absfrob's `AbsFrobDef.lean` is not copied: it is frob-contrib's `Contrib/AbsFrob/` |
| `Pieces` | `scratch/frob-pieces/part_{good,neron,final,full}.lean` | ModField opens; imports `Contrib/FrobPieces/SmoothGeomConnIntegral` |
| `LinkedStatement` | g14-trace `part_g14.lean` lines 26-30 and 146-162 (`FrobTraceLink`); linked-tate part 97 lines 15-25, 125-135 (`tmOf`) and 193-233 (`LinkedFrob`) | **one context change**, explained below; closing `end`s |
| `LinkedFrob` | `scratch/linked-frob/parts/10_linkedfrob.lean` and `parts/20_bundle4.lean` lines 1-37 | ModField opens; closing `end`s |
| `Main` | new | the closed theorems and the `Iff.rfl` checks |

**The context change in `LinkedStatement`.** g14-trace's line 31 is
`open PkgI3 G0ModNewform GlueC10Link`. Here it is replaced by
`open PkgI3 G0ModField.GaloisCopy GlueC10Link`:
- g0-mod-newform's namespace is not in this build.
- The only name of it that `FrobTraceLink` uses is `Vb`, which now resolves to
  `G0ModField.GaloisCopy.Vb`.
- Both definitions have the same body, `TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)`.
- The elaborated type is shown in §0, through `#check`.

**Not ported.** These take Leaves.lean's bundles `HSyn.TextbookLeaves`/`HSyn.ResearchLeaves`, which
are not in the kernel build:
- linked-frob's `linkedFrob_of_textbook`;
- `HSyn.GluePieces4`;
- `gluePieces3_of_gluePieces4`;
- `sixContactMin_of_leaves4`.

`linkedFrob_of_textbook` is `linkedFrob_of_neron_nmp hsp hc t.t4 t.t3`, so it adds nothing over
`linkedFrob_of_neron_nmp`, which is ported.

**Namespaces.** The declarations keep the owners' namespaces: `G0ModField`, `UnramTate`,
`G14Bridge`, `G14Trace` (only `FrobTraceLink`), `FrobTrace`, `MulRigidity`, `G0FibreSimple` (only
`RigidityHom`/`rigidityHom`), `AlgFrobRedRed`, `FrobPiecesGood`, `FrobPiecesNeron` and
`LinkedFrobRed`. Two checks show these cause no clashes:
- `Check.lean` imports the FrobChain modules together with all of contrib-check's modules
  (AbVarBC, G9 layers, TYZ, GZ, …) and compiles. So there is no clash with them (VERIFIED).
- unram-tate's BCPoints block inside `TateBridge.lean` (namespace `UnramTate`) does not clash with
  `Contrib/AbVarBC/Points.lean`, which moved that text into `ZInQ.Contrib.AbVarBC`.

Note for future adoptions:
- a port of g14-trace's `G14Trace` namespace must import `LinkedStatement` (for `FrobTraceLink`)
  instead of redefining it;
- a port of local-glue must drop its BCPoints copy, which is already in `TateBridge.lean`, as lg-kerwild did.

No Tau Ceti module was vendored, so `ThirdParty/TauCeti/NOTICE` is unchanged.

**Build results** (VERIFIED, `lake build`, this host; logs `scratch/frobchain-contrib/run_*.txt`):

| run | result |
|---|---|
| `TateBridge` | 103 s |
| first full run | `Rigidity` 7 s, `Bridge35` 12 s, `FrobTrace` 16 s, `AlgFrobRed` 42 s, `FExtend` 7 s and `Pieces` 9 s built. `LinkedStatement` failed: `GaloisCopy` is nested in `G0ModField`. Fixed by changing the context line |
| second run | `LinkedFrob` failed: without ModField's file-level opens, `GQ` was auto-bound as an implicit variable. Fixed by putting the opens before the slice, as in linked-frob's file |
| third run, and `Main` | exit 0 |

No `sorry` warning appears in any run.

## 3. Step 3: `Check.lean`

`scratch/frobchain-contrib/Check.lean` = `scratch/contrib-check/Check.lean` (unchanged) + `import
ZInQKernel.Contrib.FrobChain.Main` + the `#check`s and 32 `#print axioms` lines of §0. Building its
21 imports took 388 s (`lake build`, exit 0). The first attempt failed for lack of the olean
`ZInQ.PoleValuation`, which that build provides. Then `lake env lean
scratch/frobchain-contrib/Check.lean` gave exit 0 in 7 s, no error, and 48 standard axiom reports
(VERIFIED, `Check.out`).

`scratch/frobchain-contrib/verbatim_check.py` checks the following, with result `ALL OK` (VERIFIED,
`verbatim_check.out`):
- every one of the 18 source slices occurs character for character in its module;
- the deleted `AbsFrob` block equals frob-contrib's text;
- every chain Prop is defined exactly once, apart from the two `Iff.rfl` pairs of §1.
