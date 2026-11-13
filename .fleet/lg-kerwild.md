# lg-kerwild (2026-11-13)

**Verdict.** local-glue left two glue Props under `G15Ram.localGlue_of_unramRoots`: `KerWild` and
`DescentPts`. Both are now discharged on G7's data. No statement was changed, and neither Prop is
false, vacuous or inert.

- `KerWild` is G7Data's kernel-field clause carried through the Tate bridge. Following local-glue's
  finding G8, it was added to `TateBridge`'s output as `LGKerWild.TateBridgeK`. That bridge is
  **proved from the leaf I3.M0 alone** (`UnramTate.tateBridgeK_of_tateModuleFree`). The proof is
  unram-tate's construction, with `ScalarTransferK` adding `γ = 1 ⇒ β = a`.
- At `ℓ = 5, 3`, `TateBridge35 → TateBridge35K` is proved: `TateBridge35` already carries
  `ι_ℂ ∘ β_ℚ̄ = β`. Composed with frob-trace, this gives `TateBridge35K` from I3.M0 + `AlgFrobRed`.
- `DescentPts (A_{L'}) L` is proved for G7Data's model `A/L` (`descentPts_of_g7`). It uses
  local-glue's conjugate-model proof, and `dim A = 2` from `dim A_{L'} = 2` by g0-dim's
  base-change invariance of dimension.
- Composite: `exists_localGlue_of_tateModuleFree` (every `ℓ`) and `localGlue_of_tateBridge35`
  (`ℓ = 5, 3`). On the bridge's data, `LocalGlue` at `p ≠ ℓ` follows from R6, I2-Tors, I3.M0,
  `UnramRoots` and `G7Clauses`, with no `KerWild` and no `DescentPts`.

**Compiles (VERIFIED).** `lake env lean scratch/lg-kerwild/KerWild.lean` exits 0 with 0 errors and
no `sorry`, in about 60 s. All 21 `#print axioms` lines are standard. The file is assembled by
`build.sh` from verbatim copies of local-glue's `LocalGlue.lean`, frob-trace's `FrobTrace.lean`
(minus one duplicated block, diff-checked) and a slice of g0-dim, plus three new parts.

**Remains.**
- Integration. g0-assemble2's GLUE field 39 `LinkedTateLocal` keeps neither the transport nor
  `KerWild` (finding K2). It should be proved from `TateBridge35K` data through
  `localGlue_of_tateBridge35`.
- That route still needs `G7Clauses` for the transported data (local-data's glue, with its F3 fix
  `[L:ℚ] ≤ D`) and `TateBridge35`'s `dim`/`rank` hypotheses.
- `UnramRoots` (textbook, `p = 2`) is unchanged.

Report: `docs/research/lg-kerwild.md`. Log: `scratch/lg-kerwild/log.md`.
