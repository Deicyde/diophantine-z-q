# linked-frob results log

Target: linked-tate's glue `UnramTate.LinkedFrob` (scratch/linked-tate/parts/97_linkeddata.lean).

## Setup (2026-11-13)
- Merged origin/wip/linked-tate, origin/wip/frob-pieces (which contains alg-frob-red and afr-absfrob), origin/main.
- FINDING (VERIFIED by reading): frob-trace's `FrobTrace.AlgFrobLink` (scratch/frob-trace/part_frob.lean) gives, for one
  points-level `m` with three `DescentDatum` clauses (Galois on G_L, coset rule, algebraic `F_σ`), a finite `S` and, at every
  arithmetic Frobenius `τ` above `p ∉ S` and every `g`, one `(k, Ā, α', N)` with a `ℚ_ℓ`-iso conjugating `N·V_ℓ(m_{gτg⁻¹})` to
  `V_ℓ(α')` for all `ℓ ≠ p`; `frobCompare_opV_conjE` converts that into `FrobCompare` for `opV(Θ ∘ f ∘ Θ⁻¹)`; linked-tate's
  `tmOf … ℓ τ` is by definition `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)`. So `LinkedFrob` follows from `AlgFrobLink` with `g = h`,
  `S ∪ {3,5}`. `AlgFrobRed → AlgFrobOne → AlgFrobLink` is proved by frob-trace; `AlgFrobRed` is reduced by
  alg-frob-red / afr-absfrob / frob-pieces to N1-g1 `AbVarSpreadsOut`, `ProperSmoothGenConnected`, I2-Red, I2-NMP.
- Environment: linked-tate's statements live over `Leaves.lean` (definitions copied in-file); frob-trace & successors live
  over `import ZInQKernel.HDecomp.*`. The two cannot be imported together, so the frob chain is re-compiled over
  linked-tate's file (assemble.sh: AFR block after linked-tate's parts).
- Verbatim: py/verbatim_check.py — all sources contained verbatim in LinkedFrob.lean (two documented deletions of
  duplicate defs `G0FibreSimple.RigidityHom`, `AlgFrobRedRed.AbsFrob`, each identical to the copy that stays). VERIFIED.

## Compile outcomes
- Prefix olean (Leaves.lean + linked-tate's imports_extra + `ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral`):
  first run failed (`unknown module prefix 'ZInQ'`) until `lake build` of the five prefix imports + the Contrib module
  (9183 jobs, ok); then VERIFIED exit 0 in 570 s.
- LTail (linked-tate's 29 parts against that prefix): VERIFIED 0 errors, 32 axiom reports all standard.
- Mine.lean run 1 (AFR block + parts 10, 20): the whole AFR block (frob-trace part_bridge/part_frob, mul-rigidity,
  alg-frob-red part_red, afr-absfrob, frob-pieces) compiled unchanged over Leaves.lean; one error in part 10: `intro hNF`
  (the statement's `letI : NumberField L'` leaves no binder after elaboration). Fixed by dropping `hNF`.
- Mine.lean run 2: VERIFIED exit 0 in 79 s, 0 errors, no sorry, 109 axiom reports all standard.
- Statements proved (namespace LinkedFrobRed): `tmOf_eq`, `linkedFrob_of_algFrobLink : FrobTrace.AlgFrobLink → LinkedFrob`,
  `linkedFrob_of_algFrobRed`, `linkedFrob_of_gen` (alg-frob-red's 5 inputs), `linkedFrob_of_goodRed_nmp`,
  `linkedFrob_of_neron_nmp (AbVarSpreadsOut) (ProperSmoothGenConnected) (I2-Red) (I2-NMP)`,
  `linkedFrob_of_textbook (t : HSyn.TextbookLeaves) (AbVarSpreadsOut) (ProperSmoothGenConnected)` (t.t4, t.t3);
  `HSyn.GluePieces4` (= GluePieces3 with `linkedFrob` replaced by `abVarSpreadsOut`, `properSmoothGenConnected`),
  `HSyn.gluePieces3_of_gluePieces4`, `HSyn.sixContactMin_of_leaves4 r t gp4 : ZInQ.SixContactMin`.
- Flat file `lake env lean scratch/linked-frob/LinkedFrob.lean` (49085 lines): VERIFIED exit 0 in 628 s, 0 errors,
  no sorry, 331 `#print axioms` reports, all [propext, Classical.choice, Quot.sound] (3 line-wrapped); list in
  flat_axioms.txt.
- py/verbatim_check.py on the final flat file: all 43 checks True. VERIFIED.
