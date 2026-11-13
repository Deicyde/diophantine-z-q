# conj-pieces (fleet summary)

**Verdict.** conj-twist left three Props under G10's `ConjTwistNontrivial`. Lean now reduces all
three to leaves, with no remaining glue on the G10 path:
- **`ArtinTorsionSurj` is proved** from the existing leaf `MulIsogeny` (GluePieces2 field 1).
- **`HomLinearLift` is proved** from a new, purely analytic textbook leaf `HoloHomLift` (Mumford
  §1 + Birkenhake–Lange Prop. 1.2.1): a homomorphism `ℂ^g → B(ℂ)_σ` that is holomorphic in the
  `IsUniformization` sense factors linearly through a uniformization.
- **`ConjUniformization` is reduced** to the analytic glue `ConjHolo`. `ConjHolo` is proved for
  bijective `s`, so `ConjUniformizationNF` (number fields, the only case conj-twist uses) is a
  theorem with no hypotheses.

No statement was changed (copies checked by `diff`, substring match and `cmp`).

**What compiles.** Everything is in `scratch/conj-pieces/`. No file has a `sorry`, and every
`#print axioms` is standard. VERIFIED.
- `Artin.lean`: `artinTorsionSurj_of_mulIsogeny`.
- `Holo.lean`: `homLinearLift_of_holoHomLift`.
- `Conj.lean`: `conjUniformization_of_conjHolo`, `conjHolo_of_bijective`,
  `conjUniformizationNF`.
- `ConjPieces.lean` (conj-twist's file verbatim plus the above):
  - `conjTwistNontrivial_leaves : TateModuleFree → UniformizationExists → MulIsogeny →
    HoloHomLift → ConjTwistNontrivial`
  - `conjTwistFromLeaves_leaves : MulIsogeny → HoloHomLift → ConjTwistFromLeaves`
- `G10.lean` (g10-odd's file verbatim plus the above):
  - `g10GlueConcrete_of_leaves : MulIsogeny → HoloHomLift → G10GlueConcrete`
  - `g10Glue_of_leaves : TateModuleFree → UniformizationExists → MulIsogeny → HoloHomLift →
    G10Glue`

Build first: `lake build ZInQKernel.HDecomp.LeafPush2.T`, and `ZInQKernel.HDecomp.I3Linalg.C2`
for `G10.lean`.

**What remains.**
- The new leaf `HoloHomLift`. A Lean proof would need the complex-Lie-group structure of
  `B(ℂ)_σ`, which neither the project nor Mathlib has.
- `ConjHolo` for non-bijective `s` (glue, STANDARD). It is not used by any downstream theorem.

Report: `docs/research/conj-pieces.md`. Log: `scratch/conj-pieces/log.md`.
