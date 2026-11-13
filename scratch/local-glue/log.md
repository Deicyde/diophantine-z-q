# local-glue results log

## Step 1 (2026-11-13 06:53-07:15 PST): setup and statements
- Merged origin/wip/local-data (fast-forward of its commits onto 322303a2).
- Target: `G15Ram.LocalGlue p Tm a β L` (scratch/local-data/part_local.lean l.933), with
  `TorsionFieldWild`, `TateWildTrivialL`, `TateWildTrivial`, `BetaUpper`, `Lv`, `G7Clauses`, `U0`.
  Copy: `scratch/local-glue/LocalGlue.lean` = whole `scratch/local-data/LocalData.lean` (verbatim,
  `cat`) + `part_glue.lean` (new), assembled by `build.sh`.
- Finding G1 (logical, VERIFIED by reading): `LocalGlue` is a predicate on arbitrary
  `(Tm, a, β, L)`; it fails for `Tm = 0` at `p > D` (to be compiled: `not_localGlue_zero`).
  It is also not implied by `G7Out ∧ G8Out ∧ G7Clauses`: these tie `a·Tm` to an abelian variety
  only on `G_K` (`K = L'`), and nothing ties `K` to `L` (SPECULATIVE example: `L = ℚ`, `A = E²_K`,
  `K/ℚ` cyclic of degree `p` inside `ℚ(ζ_{p²})`, `Tm = ψ ⊗ tate(E²)` with `ψ` of order `p`,
  conductor `p²`, trivial on `G_K`; then `a·Tm(σ) = ψ(σ) ≠ 1` on some wild `σ`).
- Finding G2 (VERIFIED, read scratch/g0-mod-field/ModField.lean l.611-631): g0-mod-field's
  `G7Data` has the kernel field clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`, and `DescentDatum`
  has `A` over `L` with `m_σ` = Galois action and `a = 1` on `G_L`. g0-mod-galois's `G7Out` keeps
  only `Tm = tate`, `a = 1` on `G_K`. So at odd `p` the kernel-field clause puts wild inertia of
  `G_L` inside `G_K` (β is tame there), and the abelian-variety content is on `A/K` only.
- `lake build` of the 11 imported kernel modules started (HDecomp not prebuilt here).
