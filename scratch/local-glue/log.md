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

## Step 2 (07:02-07:12 PST): reduction compiled
- `lake build` of the 11 imported modules: ok (9075 jobs, fast: shared artifacts).
- `scratch/local-glue/LocalGlue.lean` (build.sh: verbatim LocalData.lean + part_glue.lean).
  `lake env lean scratch/local-glue/LocalGlue.lean`: exit 0, 0 errors, no sorry, ~20 s;
  `#print axioms` [propext, Classical.choice, Quot.sound] for all 7 printed (compile.out).
- Proved (VERIFIED):
  * `not_localGlue_zero (hp : D < p) L : ¬ LocalGlue (Tm := 0) (a := 1) (β := 1) L` (G1).
  * `fixSet_Lv_iff : σ ∈ fixSet (Lv L) ↔ ∀ x ∈ L, decomp p σ x = x`.
  * `beta_wild_of_clauses (p ≠ 2) : G7Clauses β ε L → σ ∈ wildSet → decomp σ fixes L →
    β (decomp σ) = 1`.
  * `aTm_eq_one_of_kerWild`, and the main reduction
    `localGlue_of_g7 : G7Out A ℓ Tm c ε a β u → G7Clauses β ε L → KerWild K β L →
     (7 ≤ p → TateWildK A ℓ) → (p ≤ 5 → TateWildKE A ℓ β L) → (p = 2 → BetaUpper β (Lv L) U0)
     → LocalGlue p Tm a β L`.
  * `tate_eq_one_of_torsFix`: σ fixes every ℓⁿ-torsion point of A(K̄) ⇒ `tate A ℓ σ = 1`;
    `tateWildK_of_torsFixWild`, `tateWildKE_of_torsFixWildE`.
- New named Props (glue): `KerWild`, `TateWildK`, `TateWildKE`, `TorsFixWild`, `TorsFixWildE`.
- Pitfall: after `open CategoryTheory`, `ι` is a token (rcases pattern fails); renamed.

## Step 3 (07:12-07:20 PST): packs
- §7: `G0ModNewform.G8LocalPack` copied verbatim from scratch/local-data/tail_part.lean;
  new `G7LocalPackK ℓ r P` (G7Out, G8Out, G7Clauses, KerWild, and at p ∈ P: TorsFixWild for
  p ≥ 7, TorsFixWildE for p ≤ 5, BetaUpper for p = 2).
- Proved (VERIFIED, compiled, axioms standard): `g8LocalPack_of_K : G7LocalPackK ℓ r P →
  G8LocalPack ℓ r P`; `g15RamG_of_packK : G7LocalPackK 5 D.r5 (· ≠ 5) → G7LocalPackK 3 D.r3
  (· = 5) → G11Out T D.r5 → G11Out T D.r3 → G15RamG D u`.
- Compile: exit 0, 0 errors, no sorry, 9 printed declarations all standard axioms.
