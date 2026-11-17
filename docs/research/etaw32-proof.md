# etaw32-proof: `EtaW32Character` proved

**Result.** The frozenTarget hypothesis `hW : ZInQ.CdOpt.EtaW32Character` (the eta-quotient transformation law
at level 32, `v(γτ) = χ₈(d) v(τ)` for `γ ∈ Γ₀(32)`, `v = η(8τ)η(32τ)²/η(16τ)³`; an instance of the
Newman / Gordon–Hughes theorem) is **proved in Lean**, from Mathlib alone (its definition of `η` and its
inversion law `eta_comp_eq_csqrt_I_inv`). No new leaf and no new hypothesis. With it, `hW` leaves
`ZInQ.OneProof.frozenTarget`: **−1, no new leaf**. All claims VERIFIED (compiled), Lean 4.35.0, Mathlib v4.35.0,
base `wip/leaf-fold33b` 0e3c3125.

| artefact | content | status |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/EtaW32Character.lean` | `ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof : ZInQ.CdOpt.EtaW32Character`; imports only `ZInQKernel.Contrib.OneProof.CdOptimal.Level32` | builds; axioms `propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`, no build-time code |
| `scratch/etaw32-proof/Discharges.lean` | `#discharges` | `DISCHARGES [hW] by …etaW32Character_proof`, still assumes `[]`, standard axioms (`discharges-output.txt`, line 198) |
| `scratch/etaw32-proof/FoldCheck.lean` | manual fold: `ZInQ.OneProof.frozenTarget_etaW32`, Main's `frozenTarget` with the binder `hW` removed and filled by the proof (body otherwise verbatim), and `frozenTarget_etaW32'` from Main's theorem | both prove `ZInQ.FrozenTarget`, standard axioms (`foldcheck-output.txt`) |
| `scratch/etaw32-proof/Target.lean` | the Prop copied verbatim, `rfl` against the kernel's | compiles |

`hW` is a binder of `frozenTarget`, so autofold cannot remove it. The integrator's fold is the edit shown in
`FoldCheck.lean`: drop `(hW : ZInQ.CdOpt.EtaW32Character)` from `Main.lean` and pass
`ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof` to `grossZagierFormulaCd_of_alg`, importing the new
module. (`Main.lean`, OPEN.md and kinds.tsv were not edited: the task rules forbid edits under `ZInQKernel/`
except the new file.)

## The proof

No generating set of `Γ₀(32)` and no numerics. The task suggested comparing two characters on a finite
generating set. That turned out unnecessary: the elements with lower-left entry `32` already reduce every element
of `Γ₀(32)`, and the law holds for all of them symbolically.

1. **Two laws for `η`.** `η(z + n) = e^{πin/12} η(z)` (`eta_add_int`, from the product definition) and Mathlib's
   `η(−1/z) = (√i)⁻¹ √z η(z)`.
2. **`η` under `z ↦ z/(nz + 1)`** (`eta_lower`, `n ≥ 1`): `z/(nz+1) = S T^{−n} S z`, so
   `η(z/(nz+1)) = e^{−πin/12} (√i)^{−2} √y √z η(z)` with `y = −1/z − n`. The branch identity
   `√y √z = i √(nz+1)` (`sqrt_mul_branch`) holds because both sides square to `−(nz+1)` and both have positive
   imaginary part (principal roots of points of `ℍ` lie in the open first quadrant). Result:
   `η(z/(nz+1)) = e^{−πin/12} √(nz+1) η(z)`.
3. **`c = 32`** (`etaD_c32`, `vC_c32`). For `γ = (a, b; 32, d)` with `a = 4A+1`, `d = 4B+1`, and
   `δ ∈ {8, 16, 32}`, `n = 32/δ`: `δ·γτ = (a−1)/n + z/(nz+1)` with `z = δτ + (d−1)/n`, `nz + 1 = 32τ + d`. Hence
   `η(δγτ) = e^{πi((a−1)/n + (d−1)/n − n)/12} √(32τ+d) η(δτ)`. In `v` the square roots cancel (`1 + 2 − 3 = 0`)
   and the exponents combine to `v(γτ) = e^{πi(A+B)/4} v(τ)`.
4. **The sign** (`exp_eq_chi8`). `(4A+1)(4B+1) − 32b = 1` gives `A + B = 4(2b − AB)` and `A ≡ B (mod 2)`, so
   `e^{πi(A+B)/4} = (−1)^{AB} = (−1)^B = χ₈(4B+1)`.
5. **All `c = ±32`** (`P_c32`, `P_c32_abs`). If `a ≡ 3 (mod 4)`, apply step 3 to `−γ⁻¹ = (−d, b; 32, −a)`. Pass
   to `γ⁻¹` and `−γ` using `(−γ)τ = γτ`, the evenness of `χ₈`, and `χ₈(a) = χ₈(d)`.
6. **`c = 0`** (`P_c0`). `γ = ±Tᵇ`, and `v` has period 1 (`vC_add_int`; exponent `8 + 64 − 48 = 24`).
7. **Reduction** (`P_of_mem`), by strong induction on `|c|`. Write `c = 32k`, `|k| ≥ 2`. From `ad − bc = 1`,
   `k ∤ a`, so some odd `s` has `|a + sk| < |k|` (`exists_odd_s`). Bezout gives `g = (u, −v; 32, s) ∈ SL(2, ℤ)`
   (`exists_row32`), and `gγ ∈ Γ₀(32)` has lower-left entry `32(a + sk)`, which is smaller in absolute value.
   The law for `g` (step 5) and for `gγ` (induction) gives it for `γ` (`P_cancel`), since
   `χ₈(d_{gγ}) = χ₈(s) χ₈(d)` when `8 ∣ c_g`.

Geometrically, step 7 is the remark that the isometric circles `|32τ + s| = 1`, `s` odd, cover the real line
except the points `k/16`. A cusp equivalent to `∞` has a reduced denominator divisible by `32`, so it never sits
at one of those points.

## What remains

Nothing for this hypothesis. Integration means the manual fold of `Main.lean` (as in `FoldCheck.lean`) and
regenerating OPEN.md. The docstring of `EtaW32Character` in `Level32.lean` still calls it a "printed leaf". It is
now a proved statement; that file is not this task's to edit.
