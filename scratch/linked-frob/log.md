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
