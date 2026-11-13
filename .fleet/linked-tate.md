# linked-tate (2026-11-13)

**Result.** g0-assemble's two joint glue Props, `ModelG3G6` and `LinkedTateData`, are proved from
strictly smaller named Props over the pin-applied `Leaves.lean`. Both statements are copied verbatim
and unchanged. Full report: `docs/research/linked-tate.md`.

- **`ModelG3G6`** follows from:
  - `FibreSimple`, an existing `GluePieces` field;
  - the new glue Prop `GoodRedTorsion`, the point-level transport half of G3;
  - the leaves R6, R7a and T5.

  The noncommutativity half of G6 is proved outright: `endBC` and `ι` are injective, and `𝒪` is
  not commutative.
- **`LinkedTateData`** follows from:
  - the leaves T7 and T26 (I3.M0);
  - `FibreSimple`;
  - three new glue Props: `QMEndRank` (rank of `End` = 4, literature-backed), `LinkedFrob`
    (g14-trace's `FrobTraceLink` for the canonical operators) and `LinkedRam` (Glazer's D1-D4 on the
    descended `ρ_ℓ`).
- **The linked ℓ = 5, 3 Tate data are constructed, not assumed.** unram-tate's construction is run
  once with one `γ₀ = β/a`, which resolves g14-trace's F1. G14 then comes from T7, and G15 is
  carried from `ρ_ℓ` to `r_ℓ` through G8's intertwiner.
- **End to end.** `HSyn.sixContactMin_of_leaves3 r t (gp3 : GluePieces3) : ZInQ.SixContactMin`.
  `GluePieces3` is `GluePieces2` with fields 27 and 28 replaced by `goodRedTorsion`, `qmEndRank`,
  `linkedFrob` and `linkedRam`, for 29 fields in all.
- **Also proved:** `LocalInertiaGlobal` and `UpperAbsInertia`, from Mathlib. Together with
  `KernelFieldBreaks` and `TateRamAtThree` they reduce `LinkedRam`, but only conditionally (next
  item).

**Finding.** g0-mod-field's `G7Data` drops `[L:ℚ] ≤ D`, although `G4Out` has it. Glue that is
universally quantified over the choices made after G7 can then fail for an oversized `L`.
- My first form of `LinkedRam` was false in that case. It is repaired by tying `γ₀` to `β/a`.
- `KernelFieldBreaks` and `TateRamAtThree` hold only when `[L:ℚ] ≤ D`.
- Recommendation: add `finrank ℚ L ≤ heightD` to `G7Data`.

Separately, g0-fibresimple's relabeling lemma (its §5) fails against the pin, as intended, and is
dropped from this task's copy.

**What compiles.**
- `scratch/linked-tate/LinkedTate.lean` is `Leaves.lean` plus every part, 45 127 lines. With
  `lake env lean` it exits 0 in 622 s with 0 errors and no `sorry`, and all 222 axiom reports are
  `[propext, Classical.choice, Quot.sound]`.
- The iteration file `olean/Tail.lean` gives the same result.

**What remains (glue).**
- `GoodRedTorsion`: transport of places, `resQ` and points; no literature beyond NOS.
- `QMEndRank`: would follow from I3.M1 plus T27 plus algebra (sketched, not compiled).
- `LinkedFrob`: Néron models and Serre–Tate.
- `LinkedRam`: D1-D4.
- `FibreSimple`: as before.
