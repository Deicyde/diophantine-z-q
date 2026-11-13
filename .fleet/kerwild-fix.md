# kerwild-fix (2026-11-13)

**I fixed the rv-fast defect, and the fix compiles.** lg-kerwild's every-ℓ theorem had a
`G7Clauses β' ε' L` hypothesis about data hidden behind `∃`. For its own witness (`a' = 1`,
`ε' = n/d`) that hypothesis was vacuous.

**The fix: Glazer's normalization.**
- The new bridge `KWFix.TateBridgeE` outputs `β' = Φ ∘ β` and `ε' = Φ ∘ ε`, where `Φ : ℂ ≃+* ℚ̄_ℓ`
  comes from Steinitz.
- The real descent factor goes into `a`.
- `tateBridgeE_of_tateModuleFree : PkgI3.TateModuleFree → TateBridgeE` is proved. The proof is
  frob-trace's construction with the embedding `j := Φ ∘ ι_ℂ`.
- `TateBridgeE` implies `TateBridge`.

**Main theorem: `KWFix.exists_localGlue_of_leaves'`.**
- For every ℓ there are `G7Out` data, and on these data `G7Clauses`, `KerWild` and `LocalGlue p`
  hold at every `p ≠ ℓ`.
- Leaves used: I3.M0, R6, I2-Tors.
- Other hypotheses: `G7Data`, `[L:ℚ] ≤ D`, `rank End(A_{L'}) = 4`.
- `UnramRoots` is now unram-roots' theorem (spliced in). `dim A_{L'} = 2` is proved.

**Also proved:**
- `[L:ℚ] ≤ D` from `G4Out`: `G7OutUnrD`, `g7OutUnrD_of_g4Out`, `exists_localGlue_of_g4Out`.
- G15's `LocalData` and `G15RamG` for G8's `r`: `exists_localData_of_leaves`,
  `exists_g15RamG_of_leaves`.
- ℓ = 5, 3 with `FrobTraceLink`: `TateBridge35E`, `tateBridge35E_of_algFrobLink`,
  `exists_localGlue35_of_algFrobRed`. These need frob-trace's glue `AlgFrobRed`.
- Both of rv-fast's open inputs on the ℓ = 5, 3 route are settled: `ε₅ = 1` on `G_L × G_L` is now
  proved, and `[L:ℚ] ≤ D` comes from `G4Out`.

**Rebuild.** lg-kerwild's parts compile unchanged against the current local-glue source.
`scratch/kerwild-fix/build.sh` no longer re-splices g0-dim.

**What compiles.** `lake env lean scratch/kerwild-fix/KerWildFix.lean`: 0 errors, about 73 s.
All 22 `#print axioms` lines show only `[propext, Classical.choice, Quot.sound]`. No `sorry`.

**What remains:**
- `rank End(A_{L'}) = 4` is still a hypothesis (glue `EndRank4`).
- The `G8Out` link from these data to G8's `r_ℓ` is not made.
- `AlgFrobRed` is still needed at ℓ = 5, 3.
- Nothing is wired into g0-assemble2's `GluePieces3`.
- frob-trace's proof is duplicated twice in the new part; it should be factored at integration.
- Restating the data in local-glue's `G7LocalPackBC` (over `bcL'`) timed out, so G15 is reached
  through `g15RamG_of_g7` instead.
- Model review only.

Report: docs/research/kerwild-fix.md. Log: scratch/kerwild-fix/log.md.
