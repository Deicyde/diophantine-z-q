# redei-kernel report

## Proved

`ZInQKernel/RouteK/Redei/Kernel.lean` (namespace `ZInQ.RouteK.Redei`), with the root module
`ZInQKernel/RouteK/RedeiKernel.lean`, which `ZInQKernel.lean` imports. This is step 7 of
docs/research/redei-plan.md §3.2.

- `kernel_trivial_iff_redeiG`: the statement is copied word for word from
  `scratch/redei-plan/Probe.lean` §3.7, with no changes. Hypotheses: `Recip a y` and `B.Nonempty`.
  The kernel of `(L_B | z_B)` (the column `z_B` only when `y(B) = 0`) is `{0, 1_B} × {e₂ = 0}` iff
  `redeiG a y z B = 1`.
- Helpers, all with the prefix `redeiK_` so they cannot clash with sibling names:
  - `redeiK_lapl_rowSum`: the rows of `L_B` sum to zero over `B`.
  - `redeiK_det_updateCol`: `det (L_B with column ρ replaced by w)[B,B] = Σ_{v∈B} w_v κ_v(B)`.
    Proof: transpose (`pmin_transpose`), expand along row ρ (`pmin_expand_row`), then Lemma 2.2(2)
    (`pmin_lapl_offdiag`).
  - `redeiK_sum_updateCol`: splits off column ρ.
  - `redeiK_ker_iff_det`: trivial kernel iff nonzero determinant, for vectors `ι → 𝔽₂` supported on
    `B` (`Matrix.exists_mulVec_eq_zero_iff`).
  - `redeiK_kernel_iff_updateCol`: the kernel of `(L_B | z_B)` is trivial iff `N_w` has trivial
    kernel. Here `N_w` is `L_B` with column ρ replaced by `w = if y(B) = 1 then y else z`.
  - `redeiK_zmod2_cases`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`. A `#guard_msgs` `#print axioms` check in
  `RedeiKernel.lean` enforces this.
- Builds: `lake build ZInQKernel.RouteK.RedeiKernel` and `lake build ZInQKernel` both succeed. There
  is no `sorry`.

## Mathematics (how the proof goes)

Fix ρ ∈ B. The proof handles both cases at once:
- If y(B) = 1, take w = y. Then `det N_w = Σ y_v κ_v = redeiG` by the definition of `redeiG`.
- If y(B) = 0, take w = z. Then `det N_w = Σ z_v κ_v = redeiG`.

The kernel reduction rests on three facts:
- The rows of `L_B` sum to zero, so `1_B` is in the kernel and every kernel vector can be shifted
  until `e_ρ = 0`.
- If y(B) = 1, the column sums of `L_B` vanish (`colSum_lapl`) and `Σ_B y = 1`. Summing the rows of
  `N_y f = 0` then forces `f_ρ = 0`.
- If y(B) = 0, `f_ρ` plays the role of `e₂`.

Lemma 2.2(1) (`kappa_eq_kappa`), which the plan listed, turned out not to be needed: the definition
of `redeiG` already uses `Σ y_ρ κ_ρ`.

## Problems / notes

- `lake env lean` on a single file fails in a fresh worktree because the `z_in_q` package (`lean/`)
  is not built. Use `lake build <module>` instead.
- `scripts/print_axioms.lean` is unchanged, because the task named no lines there.

## Suggestions

- In step 8 (Bridge), apply `kernel_trivial_iff_redeiG` with `a = aBit d`, `y = yBit d`,
  `z = zBit d`, restricted to `B`. The reciprocity hypothesis is `Sec3.recip_bits` (`RouteK/Rank5b/Sec3/TYZ.lean`).
