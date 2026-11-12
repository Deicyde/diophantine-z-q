# glue-assembly: results log

Task: glue clusters C8, C10, E1, E3, E4, F2 of `docs/research/h-trust.md`; Lean proofs of the
elementary parts in `scratch/glue-assembly/`. Marks: VERIFIED (read in a source, computed, or
compiled), STANDARD (published, exact reference), SPECULATIVE. Theorem numbers recalled from memory
are UNVERIFIED.

## Step 0 (start, 2026-11-11)

- No earlier run (no log). Branch `wip/glue-assembly` at a4355d3e.
- Sources read: h-trust §0-§1 C1-F4; N5 L377-403 (constants), L578-631 (CM branch), L719-800
  (C1-C10), L855-972 (D5-F4); wk-h §§1-6 (with `scratch/wk-h/Arakelov.lean`, whose
  `transfer_numerics` already proves the E3-E4 arithmetic as a real lemma);
  `ZInQKernel/Hypotheses/{Height,HeightMin,JHeight}.lean`.
- VERIFIED (ls): `.lake/build/lib/lean/ZInQKernel/Hypotheses/JHeight.olean` exists in this
  worktree, so scratch files can `import ZInQKernel.Hypotheses.JHeight` (unlike wk-h's worktree).
- VERIFIED (read Mathlib v4.35 `NumberTheory/Height/{Basic,MvPolynomial,NumberField}.lean`):
  `Height.logHeight` (projective, relative to `K`, with `AdmissibleAbsValues`),
  `logHeight_eval_le` (degree-`N` homogeneous map, explicit `mulHeightBound`),
  `logHeight₁_div_eq_logHeight`, `NumberField.mulHeight_eq`, `totalWeight_eq_finrank`,
  `Rat.logHeight₁_eq_log_max`. No lemma relating `logHeight₁ (algebraMap ℚ K q)` to the height of
  `q` over `ℚ` (the "height invariance under extension" that wk-h §4.2 flagged).

## Step 1: F2 over Mathlib's Weil height (VERIFIED: compiled)

- `scratch/glue-assembly/F2.lean` (`lake env lean`, no errors, no `sorry`; 6 s):
  `GlueAssembly.logHeight_Phi_le`: for any field `K` with `Height.AdmissibleAbsValues` and
  `z : Fin 10 → K`,
  `logHeight ![3779136 (∏ z_i)⁴, (∑ z_i⁸)⁵] ≤ 40 logHeight z + totalWeight K · log 3779136`;
  `logHeight₁_Phi_le`: the same for the quotient `Φ(z)`. Proof: Mathlib's `logHeight_eval_le` for
  the two degree-40 forms (defined over `ℕ` and mapped), and `mulHeightBound ≤ 3779136^{n_K}`
  (archimedean `ℓ¹` norms `≤` value at `1`: `3779136` and `10⁵`; nonarchimedean factors `= 1`).
- `scratch/glue-assembly/Ext.lean` (compiled, no errors): `logHeight₁_algebraMap_rat`:
  for a number field `K` and `q : ℚ`, `logHeight₁ (algebraMap ℚ K q) = [K:ℚ] · log max(|num q|, den q)`
  (via the coprime pair `[num : den]`: finite places give `1`, infinite places give `max(|a|,|b|)`,
  `∑ mult = [K:ℚ]`). This is the invariance under extension that wk-h §4.2 found missing.

## Step 2: E-arithmetic, CM arithmetic, F3 arithmetic, assembly (VERIFIED: compiled)

- `scratch/wk-h/Arakelov.lean`'s `transfer_numerics` re-proved in `Transfer.lean`; new:
  `transfer_of_level` (from `N ≤ QM²`, Javanpeykar's `1.3·10⁷N¹²`, `2 ≤ g ≤ N²`, `d ≤ QM`, GR14,
  variation+additivity, Bost `h_F(Z) ≥ −(3/2)g` ⇒ `h_F(A) ≤ Q¹⁷M²⁴`); `cm_numerics` and
  `log_two_mul_bcm_le` (N5 L606-628: `h_F(A) ≤ 2B_cm + 4096(1028 + 5D + 84000D²) = C_cm`, with
  `log 28 ≤ 4`, `log 3, log 4 ≤ 2`); `pazuki_numerics` (N5 L934-947:
  `h ≤ X_D/2 + C₂ log(X_D+2)` ⇒ `h ≤ 10⁴·2²⁴·max(1, h_F(A))`, with `log π ≤ 2`, `log 16 ≤ 3`).
- Scratch cannot import `ZInQKernel.Hypotheses.JHeight` after all (VERIFIED: "unknown module prefix
  'ZInQ'": its import chain reaches the unbuilt upstream `lean/`). `F4Copy.lean` copies JHeight's
  F4 part verbatim and states `SixContactMinAt S` (`= SixContactMin` at `S = Mult.S_mul` by `rfl`).
  `ZInQKernel.Compiler.Precision.HeightConstant` (imports only `Hypotheses.Height`) is importable.
- `Assembly.lean`: `GlueOutputs S` (per `u ∉ 𝒞`: number field `K`, theta point `z : Fin 10 → K`
  with `Φ(z) = J(u)` in `K`, Pazuki's bound for `h_K(z)/[K:ℚ]`, and the numerical outputs of either
  the non-CM transfer at `Q = Q_D`, `M = M_S(u)` or the CM branch);
  `sixContactMinAt_of_glueOutputs : GlueOutputs S → SixContactMinAt S`.
- `build.sh` concatenates F2, Ext, Transfer, F4Copy, Assembly into `GlueAssembly.lean`
  (≈ 900 lines). `lake env lean scratch/glue-assembly/GlueAssembly.lean`: no errors, no `sorry`;
  `#print axioms sixContactMinAt_of_glueOutputs`: `[propext, Classical.choice, Quot.sound]`.
- Kernel trap met (VERIFIED): `rw [heightCcm_eq_ccmFn, ccmFn_eq]` under a cast to `ℝ` makes the
  kernel evaluate `Nat.pow` ("does not fit in a 32-bit unsigned integer"); fixed by proving the CM
  bound over variables (`cm_branch_nat`) and applying it to `heightBcm_eq`, `heightCcm_eq`.

## Step 3: C8 glue, F3 glue, statable leaves (VERIFIED: compiled, no `sorry`)

- `C8.lean`: `weight_match` (`{n, n+1−k} = {0,−1}`, `k ≥ 1` ⇒ `k = 2`, `n = 0`);
  `weight_match_coh` (`{n, n+k−1} = {0,−1}` ⇒ `k = 2`, `n = −1`, Pan's normalization; agrees with
  rv-h-c8 `weights.py`); `finite_range_of_finiteIndex` (a hom with finite image on a finite-index
  subgroup has finite image); `finite_range_of_sq` (`ψ : G →* Eˣ`, `E` a field, `ψ²` of finite
  image ⇒ `ψ` of finite image); `twist_finite` (h-trust C8 items 1-3 assembled: `r = ε χ ψ²`,
  `r² = χ²` on a finite-index `H`, `ε` of finite image ⇒ `ψ` of finite image).
- `F3Glue.lean`: `mulHeightL2` (projective height with the `L²` norm at archimedean places) and
  `mulHeight_le_mulHeightL2` (N5 L938-939: the Euclidean height dominates the sup height);
  `logHeight_sixteen_eq` (six zero odd theta constants); `mulHeight_rootsOfUnity_mul` (roots of
  unity on coordinates). Whether `mulHeightL2` is exactly Pazuki's normalization: UNVERIFIED (Pazuki
  2012 not readable here).
- `Leaves.lean`: `KroneckerWeber` and `BrauerNesbittCharZero` as `def … : Prop` over Mathlib
  objects (`CyclotomicField`, `Representation`, `IsSemisimpleRepresentation`,
  `Representation.Equiv`). These are the only leaves of the cluster statable in Mathlib today.

## Step 4: report, and E2's index bound (VERIFIED: compiled)

- `docs/research/glue-assembly.md` written (statements, leaves, glue, Lean status of C8, C10, E1,
  E3, E4, F2, F3 glue, assembly).
- `E2Index.lean`: `index_Gamma1_le : (Gamma1 N).index ≤ N ^ 2` for `[NeZero N]`, via
  `firstColMod_eq_iff` (first column mod `N` equal ⇔ `a⁻¹b ∈ Γ₁(N)`). Compiled, no `sorry`.
  Note: Mathlib's `Matrix.SpecialLinearGroup.coe_mul`/`coe_inv` do not `rw` against
  `(x : Matrix (Fin 2) (Fin 2) ℤ)` written in a client file (instance-path mismatch); they are
  `rfl`, so state the needed equation with `:= rfl` and rewrite with that.
