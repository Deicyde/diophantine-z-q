# linked-frob (2026-11-13)

**Main result.** linked-tate's glue `UnramTate.LinkedFrob` (unchanged, verbatim from
`scratch/linked-tate/parts/97_linkeddata.lean`) is proved from strictly smaller Props:
- `LinkedFrobRed.linkedFrob_of_algFrobLink : FrobTrace.AlgFrobLink → UnramTate.LinkedFrob`. This step
  is new. It takes `g = h` in frob-trace's `AlgFrobLink` and `S ∪ {3,5}`, then applies frob-trace's
  `frobCompare_opV_conjE`; `tmOf … ℓ τ = opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)` holds by `rfl`.
- Through the chain of earlier tasks (frob-trace, alg-frob-red, afr-absfrob, frob-pieces), compiled
  again here:
  - `LinkedFrobRed.linkedFrob_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) : UnramTate.LinkedFrob`;
  - `linkedFrob_of_textbook (t : HSyn.TextbookLeaves) hsp hc`, which takes I2-Red and I2-NMP as `t.t4`
    and `t.t3`.
- Also proved: `tmOf_eq`, `linkedFrob_of_algFrobRed`, `linkedFrob_of_gen` and
  `linkedFrob_of_goodRed_nmp`.
- New bundle `HSyn.GluePieces4`: `GluePieces3` with the field `linkedFrob` replaced by
  `abVarSpreadsOut` and `properSmoothGenConnected`. Proved for it:
  - `HSyn.gluePieces3_of_gluePieces4`;
  - `HSyn.sixContactMin_of_leaves4 r t gp4 : ZInQ.SixContactMin`.

**Compiles.** `lake env lean scratch/linked-frob/LinkedFrob.lean` (49 085 lines, from `assemble.sh`):
exit 0 in 628 s, no `sorry`, 331 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`.
- The file is linked-tate's prefix and parts, then the frob chain block, then `parts/10_linkedfrob.lean`
  and `parts/20_bundle4.lean`.
- `py/verbatim_check.py` gives 43/43 True.
- Finding: the frob chain was written over `import ZInQKernel.HDecomp.*`, yet it compiles unchanged
  over linked-tate's `Leaves.lean`. Only two duplicate `def`s, identical text, were dropped.

**Remains.** neron-lg's N1-g1 `AbVarSpreadsOut` and frob-pieces' leaf candidate
`ProperSmoothGenConnected`. Neither is owned by this task. No new Props were introduced.

Report: `docs/research/linked-frob.md`. Log: `scratch/linked-frob/log.md`.
