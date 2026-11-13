# p-side: P1–P5 for L(C_d, s), all proved

**Result.** All five positive-rank targets are proved in Lean, with no `sorry`. Every headline
theorem uses only `propext`, `Classical.choice` and `Quot.sound` (22 checked:
`scratch/p-side/axioms-output.txt`). The code is seven new modules under
`ZInQKernel/Contrib/PSide/`, about 1000 lines. They import only baseline files and Mathlib, nothing
imports them, and no existing file was edited.

- **P1** (`APZero.lean`): `a_p(C_d) = −Σ_x χ(x³ − d²x)`. For `p ≡ 3 (mod 4)` with `p ∤ 2d` this
  gives `a_p = 0` and `#C_d(𝔽_p) = p + 1`.
- **P2** (`Coeff.lean`): API for `cdCoeff`, mostly for every `d`:
  - multiplicativity on coprime arguments (`IsMultiplicative`);
  - prime powers as power-series coefficients, and `c_p`;
  - the recursion `c_{p^{k+2}} = c_p c_{p^{k+1}} − p c_{p^k}` for `p ∤ 2d`;
  - vanishing at `p ∣ 2d`;
  - `LFunction = cdCoeff` for odd squarefree `d`.
- **P3** (`BadPrimes.lean`): `a_p = p − #{y² = x³ − d²x}` also at `p ∣ 2d`, so at every prime.
  At `p ∣ d` the reduction is a cusp with `p` affine points; at `p = 2` there are 2 points.
- **P4** (`Hasse.lean`, `Convergence.lean`):
  - Hasse's bound `c_p² ≤ 4p` for every prime and every `d`, by Jacobsthal sums and Mathlib's
    Jacobi sum, not general Hasse;
  - `|c_n| ≤ σ₀(n)√n`;
  - Mathlib's `L(C_d, s)` converges absolutely for `Re s > 3/2` (`LSeriesSummable_cd`), has
    abscissa `≤ 3/2`, and is holomorphic there.
- **P5** (`TYZInputsIff.lean`):
  - `tyzInputs_iff`: `TYZInputs ↔ ∀ n ≡ 5 sqfree, (continuation of order ≤ 1) ∨ (T5a = T5b = 0)`;
  - `tyzInputs_iff_readingA`: `TYZInputs ↔ TYZThm35ReadingA ∧ ∀ n, (∃ cont) ∨ (T5a = T5b = 0)`,
    with no hypothesis;
  - under `HeckeContinuation`, `TYZInputs ↔ TYZThm35ReadingA`.
- **Extra** (`Supersingular.lean`): `c_{p^{2k}} = (−p)^k` and `c_{p^{2k+1}} = 0` at `p ≡ 3 (mod 4)`.

**Checks.** `lake build` of all seven modules succeeds. A PARI cross-check on 30 inputs (`d = 5`,
`n ≤ 30`) agrees with every formula.

**What remains.** No registered provider is closed; this is glue and API on the CR₃ side. Two
docstrings could point to the new files but are pinned, so I left them alone:
- `RouteK/PropN.lean` around L1522 still says `tyzInputs_iff` is not in Lean;
- `STATUS.md`.

The Hasse bound covers `C_d` only. Details: `docs/research/p-side.md`; log: `scratch/p-side/log.md`.
