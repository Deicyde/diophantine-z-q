# frob-pieces (2026-11-13)

**Main result.** `FrobTrace.AlgFrobRed` now rests on four inputs:
- neron-lg's glue N1-g1 `AbVarSpreadsOut`;
- a new leaf candidate `ProperSmoothGenConnected` (Zariski's connectedness theorem, EGA III₁ 4.3);
- the kernel leaves I2-Red and I2-NMP.

The theorem is `FrobPiecesGood.algFrobRed_of_neron_nmp` in `scratch/frob-pieces/FrobPiecesFull.lean`.
It combines this task's results with afr-absfrob's `absFrob` and `fExtendGen_of_nmp`. Its axioms are
`[propext, Classical.choice, Quot.sound]` (VERIFIED). The `TateBridge35` companion is
`tateBridge35_of_neron_nmp`. alg-frob-red's statements were not changed.

**Proved.** All of these have the three standard axioms only.
- `FrobPieces.smoothGeomConnIntegral : SmoothGeomConnIntegral`, a verbatim copy of alg-frob-red's
  leaf candidate. It is in `ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean`.
  - The proof is Tau Ceti's `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral` (smooth and
    geometrically connected imply geometrically integral). The other ten modules of its closure were
    vendored unmodified from commit 5a01f5fe, with a NOTICE entry; diffcheck2 is clean.
  - In the scratch assembly, `FrobPiecesGood.smoothGeomConnIntegral : AlgFrobRedRed.SmoothGeomConnIntegral`.
- `FrobPiecesGood.goodRedCofinite_of : AbSchemeSpreadsOut → GoodRedCofinite`. `AbSchemeSpreadsOut` is a
  new leaf candidate: the published spreading-out statement, an abelian scheme over a finitely
  generated `ℤ[s] ⊆ L`.
- `FrobPiecesNeron.goodRedCofinite_of_neron : AbVarSpreadsOut → ProperSmoothGenConnected →
  GoodRedCofinite`. The proof:
  - `S` is the set of prime factors of `|N(f)|`;
  - `𝓞_L[1/f] → O_w` comes from `IsLocalization.Away.lift`;
  - the abelian scheme is base-changed to `O_w` (`hasGoodReduction_of_base`, which uses
    `Over.pullbackComp` and `mapGrpNatIso`).
- Final forms: `algFrobRed_of_neron_nmp`, `algFrobRed_of_spread_nmp`, `algFrobRed_of_goodRed_nmp`,
  `tateBridge35_of_neron_nmp` and `tateBridge35_of_spread_nmp`. Forms that keep `FExtendGen` and
  `AbsFrob` as inputs are also proved: `algFrobRed_of_neron`, `algFrobRed_of_spread`, `algFrobRed_of_four`.

**What compiles.** Every run exits 0 with no `sorry`:
- `lake build ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral`;
- `lake env lean scratch/frob-pieces/FrobPieces.lean`, 99 axiom prints;
- `lake env lean scratch/frob-pieces/FrobPiecesFull.lean`, 114 axiom prints, about 2-3 min.

The two scratch files are assembled by `build.sh` and `build_full.sh` from `cmp`-identical copies of
alg-frob-red's `AlgFrobRed.lean` and of afr-absfrob's `AfrAbsFrob.lean`. `py/verbatim_check.py` confirms
that the copied Props are verbatim.

**Review.** One read-only model review, no human review: both new Props are TRUE and non-vacuous.
Its docstring wording fixes were applied.

**What remains.**
- `AbVarSpreadsOut` (N1-g1). Mathlib v4.35 has no descent of schemes, properness or smoothness.
- `ProperSmoothGenConnected`. Mathlib has no Stein factorization.
- The kernel leaves I2-Red and I2-NMP.

Report: `docs/research/frob-pieces.md`. Log: `scratch/frob-pieces/log.md`.
