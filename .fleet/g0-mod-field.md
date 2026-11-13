# g0-mod-field (G2, G4, G7: fibre field, Hom field, scalar descent to L')

**Main result.** `scratch/g0-mod-field/ModField.lean` compiles with no `sorry`, and its main
theorems use only `propext`, `Classical.choice` and `Quot.sound` (VERIFIED, `lake env lean`). For
every fibre context (`FibreCtx`: R1-R2 clauses, `u ∉ 𝒞`, a `ℚ̄`-object `P` over `J(u)`),
`fieldDescentUnr` proves G7's output `G7OutUnr u P`. Its inputs are three glue Props and four
leaves:
- glue: `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4: Weil restriction,
  Galois image in `GL_r(ℤ)`, conjugacy isogenies `ConjugacyData`), `UnramifiedSup` (a compositum of
  unramified fields is unramified; STANDARD);
- leaves: T14-T15 (or glue-descent's `LeafHasse`, `LeafLocalTwo`), T30 (`LeafSqrtCrit`) and
  T31 (`LeafUnramified`).

The output `G7Data` contains: the Hom field `L` (`[L:ℚ] ≤ D`); the model `A/L` with its descent
datum (maps `m_σ = μ_σ∘σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`); `χ` and `β` with `β² = χ`,
`∂β = ε`; `L' ⊇ L` with `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M_{S_mul}(u)` and `L'` unramified
outside `T`; and `A_{L'}` a model of `P`.

`modularConstituent_of_ranges_T14` proves g0-split's `ModularConstituent` (over `PkgI3.AbVar`)
from these inputs plus `AfterG7`, which bundles G8-G16 (the other two tasks).

**Proved Lean.** In order: G2's degree bookkeeping (`g2Out_of_cover`); B1's normalization
(`descentDatum_of_conjugacy`: `a_σ = |ker m_σ|^{-1/4}`, `ε = sgn c`); G4's bookkeeping (Minkowski,
`[E⊔K:ℚ] ≤ D`, the model by base change); B2-B3 on the actual datum, with B3(v)'s twist
(`g7OutUnr_of_g4Out` through `b3_of_cochain` and `unramified_outside_noLeaf`); and transitivity of
base change (`baseChangeTrans`).

**Found.** The first draft did not constrain `a_σ` on `G_L`, which left it free up to a positive
character. The fix: `a = 1` on `G_L`, inflated. The fix is now proved from kernel sizes.

**Remains.** `FibreCoverExists`, `KernelFieldExists` and `UnramifiedSup` as above. Also a bridge
from `G7Data` to g0-mod-galois' per-`ℓ` `G7Out`: the Tate functor on `m_σ`, coefficients into
`ℚ̄_ℓ`, matrix units and continuity (docs/research/g0-mod-field.md §3). Every truth check of the
Props is a model check, with no human review.

Report: docs/research/g0-mod-field.md. Log: scratch/g0-mod-field/log.md.
