# frobchain-contrib (2026-11-13): fleet summary

**Main result.** The closed frob chain (frob-trace, mul-rigidity, alg-frob-red, afr-absfrob via frob-contrib's
`Contrib/AbsFrob/`, frob-pieces, linked-frob) is now in the kernel's Contrib build: 10 new modules under
`ZInQKernel/Contrib/FrobChain/`, all built with `lake build`, no existing file changed, no Tau Ceti vendoring.
Proved (VERIFIED, axioms [propext, Classical.choice, Quot.sound]), in `FrobChain/Main.lean`, namespace
`ZInQ.Contrib.FrobChain`:
- `algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
  (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FrobTrace.AlgFrobRed`
- `tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree) hsp hc hRed hN : G14Bridge.TateBridge35`
- `linkedFrob_of_neron_nmp hsp hc hRed hN : UnramTate.LinkedFrob`
- `frobTraceLink_copy_iff` (G14Bridge.FrobTraceLink ↔ G14Trace.FrobTraceLink), `smoothGeomConnIntegral_copy_iff`
  (AlgFrobRedRed ↔ FrobPieces), `kernel_leaves_iff` (ObjBridge ↔ PkgI2 forms of I2-Red, I2-NMP), all `Iff.rfl`.
The owners' theorems are compiled under their own names too (FrobPiecesGood.*, LinkedFrobRed.*, FrobTrace.*,
AlgFrobRedRed.*, G0FibreSimple.rigidityHom, UnramTate.tateBridge_of_tateModuleFree).

**Statement check.** None of the chain's glue Props is a kernel definition (grep of 86 names over ZInQKernel/);
the kernel Props involved (I2-Red, I2-NMP, I3.M0, FrobCompare) are used directly, not copied. `LinkedFrob` (linked-tate,
written over Leaves.lean) is compiled from its verbatim text over the kernel + g0-mod-field/unram-tate.

**What compiles.** `scratch/frobchain-contrib/Check.lean` (contrib-check + FrobChain.Main): exit 0, 48 axiom reports,
all standard. `AxiomAudit.lean`: all 572 declarations of `ZInQKernel.Contrib.FrobChain.*` standard. `verbatim_check.py`:
all 18 slices verbatim, ALL OK. Generator: `scratch/frobchain-contrib/build_modules.py`.

**What remains.** Open inputs: N1-g1 `AbVarSpreadsOut` and `ProperSmoothGenConnected` (scratch Props), the kernel
leaves I2-Red/I2-NMP (T4/T3) and, for TateBridge35, I3.M0 — no proof of these three kernel Props was found in the
worktree. Not ported (need Leaves.lean's HSyn bundles): `linkedFrob_of_textbook`, `HSyn.GluePieces4`,
`sixContactMin_of_leaves4`. Report: docs/research/frobchain-contrib.md.
