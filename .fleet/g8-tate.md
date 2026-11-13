# g8-tate (2026-11-13)

**Result.** The glue left under G8 (g8-object §4) is closed in Lean, modulo two existing named glue
Props. g8-object's `LinkedTateObjS` and `LinkedTateDataD` are copied verbatim. Both are the
restated `GluePieces2` field `linkedTateData`, for G7 data with `[L:ℚ] ≤ D`. Both are now proved
from:
- the leaves R6, I2-Tors, T26 (and T7 for `LinkedTateDataD`);
- local-glue's textbook Prop `UnramRoots 2 5`;
- the glue `EndRank4` (`rank End(A_{L'}) = 4`, the content of linked-tate's `FibreSimple` +
  `QMEndRank`);
- linked-tate's glue `LinkedFrob` (`FrobTraceLink` for the canonical operators).

No statement was changed. The theorems are `G8Tate.linkedTateObjS_of_frob` and
`G8Tate.linkedTateDataD_of_frob`.

**Item by item:**
- `WildTateTrivial`, `BetaUpperC`/`BetaTameC` and the local field `F` are all proved
  (`localDataS_of_g7Data`). At `p = 2` the input is `UnramRoots`; T16 is not used.
- `OnL` is proved outright for unram-tate's canonical operators (`onL_canon`). The isomorphism is
  `ψ⁻¹ = V(m_x) ∘ V(Θ ∘ trPt φ₁)`; the descent isogeny `m_x` is needed.
- `TateBridge35`'s data are built from linked-tate's construction with rescaled scalars
  (`aQ = βQ/γ₀∘conj_h`, `βQ = κ⁻¹ ∘ β`), so that `ιC ∘ βQ = β` and `aQ = 1` on `G_L`. This is
  `tateBridgeOnL_of`.

**Tools:** `exists_complex_equiv` (`ℂ ≃+* ℚ̄_ℓ`, Steinitz) and `exists_finGal_tame` (Galois closure
of a degree-`< p` field is tame).

**What compiles (VERIFIED).** `lake env lean scratch/g8-tate/G8Tate.lean` (12 858 lines, written by
`build_flat.sh`) gives 0 errors and no `sorry`. All 147 `#print axioms` reports are
`[propext, Classical.choice, Quot.sound]`. The flat file is g8-object's `G8Object.lean`,
local-data/local-glue's parts and linked-tate's parts 96-97, all verbatim, plus the new parts
`part_tools`, `part_local`, `part_link`, `part_onl` and `part_tb`. One model review was done, and
its fixes are applied.

**What remains:**
- `EndRank4` (Albert's classification, via linked-tate's Leaves-layer `FibreSimple`);
- `LinkedFrob` (reduction mod `p` and Serre–Tate; G14 content);
- `UnramRoots 2 5` (textbook);
- integration: add `[L:ℚ] ≤ D` to `G7Data`. Then `linkedTateDataD_of_frob` replaces the fields
  `linkedFrob` + `linkedRam` of `GluePieces3` by `EndRank4` + `LinkedFrob` (`LinkedRam` is no longer
  needed).

Report: `docs/research/g8-tate.md`. Log: `scratch/g8-tate/log.md`.
