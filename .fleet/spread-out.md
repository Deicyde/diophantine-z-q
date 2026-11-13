# spread-out (2026-11-13) — summary

**Main result.** neron-lg's glue N1-g1 `AbVarSpreadsOut` is reduced to three published EGA IV
theorems, stated as leaves in published form (locators UNVERIFIED): `EGAIV_8_8_2_ii` (descent of
schemes of finite presentation), `EGAIV_8_10_5_xii` (descent of properness), `EGAIV_17_7_8_ii`
(descent of smoothness), all in `ZInQKernel/Contrib/SpreadOut/Spread.lean`. Everything around them
is proved: `L = colim 𝓞_L[1/n!]`, the descent of group law/unit/inverse/axioms from Mathlib's
EGA IV 8.8.2 (i) (Stacks 01ZC), and the transfer to every presentation of `𝓞_L[1/f]`.
`AbVarSpreadsOut` itself is NOT proved outright (the three leaves are open; not in Mathlib 4.35
or Tau Ceti).

**Declarations proved** (no sorry; axioms propext, Classical.choice, Quot.sound):
* `ZInQ.SpreadOutN1.abVarSpreadsOut_of_ega : EGAIV_8_8_2_ii → EGAIV_8_10_5_xii →
  EGAIV_17_7_8_ii → AbVarSpreadsOut` (scratch/spread-out/SpreadOut.lean; `AbVarSpreadsOut`,
  `HasAbelianSchemeAway` verbatim from scratch/neron-lg/NeronLG.lean, checked by
  scratch/spread-out/py/verbatim_check.py).
* `ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega` (the unfolded body; Contrib/SpreadOut/NumberField.lean),
  `ZInQ.Contrib.SpreadOut.exists_grpObj_descend` (smooth proper group schemes over a directed limit
  of qcqs schemes with affine transitions descend, from the leaves), `exists_lift`, `exists_map_eq`
  (Over-form EGA IV 8.8.2 (i)), `isMonHom_descend` and the abstract group-descent lemmas,
  `NF.ringCoconeIsColimit`, `NF.specConeIsLimit`.
* `ZInQ.SpreadOutFull.algFrobRed_of_ega_nmp` (`FrobTrace.AlgFrobRed` from the three EGA leaves,
  `ProperSmoothGenConnected`, I2-Red, I2-NMP), `tateBridge35_of_ega_nmp`,
  `frobPiecesNeron_abVarSpreadsOut` (scratch/spread-out/SpreadOutFull.lean = frob-pieces'
  FrobPiecesFull.lean + this task; N1-g1 no longer needed there).

**What compiles.** `lake build ZInQKernel.Contrib.SpreadOut.NumberField` (4 new Contrib files:
GrpDescent, Limit, Spread, NumberField); `lake env lean scratch/spread-out/SpreadOut.lean` exit 0
(~5 s); `lake env lean scratch/spread-out/SpreadOutFull.lean` exit 0 (2 min 23 s, 117 axiom
prints, all standard, no sorry).

**What remains.** The three EGA IV leaves (large formalizations: descent of fp algebras + gluing
data for 8.8.2 (ii); constructibility arguments for 8.10.5 (xii) and 17.7.8 (ii)). Report:
docs/research/spread-out.md; log: scratch/spread-out/log.md.
