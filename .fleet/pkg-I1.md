# pkg-I1 (discriminant-6 Shimura curve: h-trust A2-A5, A7, A10, F1) — report

**Main result.** I wrote A2 + F1 as a concrete Lean leaf with no Shimura curve or abelian variety
in it: `QMHauptmodul` (scratch/pkg-I1/I1.lean). It uses an explicit period matrix `Ω(τ)` of N5's
QM datum, computed here, and the ten even genus-2 theta constants, defined as `tsum`s over `ℤ²`.
The leaf says that `j_θ = 3779136(∏θ_m)⁴/(Σθ_m⁸)⁵ ∘ Ω` is a Hauptmodul of `Γ*\ℍ`
(`Γ* = ι(N_B(𝒪)⁺)` acting through Mathlib's `GL(2,ℝ)` action), with values `0, ∞, −16/27` at the
fixed points of `ι(x)` for `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`, `x² = −6`. It is a
consequence of Lin–Yang Ex. 30, Igusa 1967 and Baba–Granath. Checked numerically (30 digits):
invariance under the generators of `Γ*`, the three CM values, a simple pole on the quotient at
`i√3`, and `81/64` at a disc −19 point.

**Leaves** (docs/research/pkg-I1.md §2):
- statable and compiled: I1-b `QMHauptmodul`; I1-c `ThetaModularity` (Igusa: `Σθ⁸`, `∏θ²` of
  weight 4 and 10 for `Sp₄(ℤ)`; signs checked numerically); I1-g `IgusaClebschSeparation`
  (Clebsch–Bolza–Igusa, with explicit `J₂…J₁₀` polynomials checked against PARI);
- statable, not drafted: I1-f, Vignéras' local normalizers (A3);
- not statable today: I1-a, the canonical model as the fine moduli scheme over `ℚ` with its
  uniformization and Hecke action (Shimura, Deligne, Kottwitz: A4, and the `ℚ`-structure of A2);
  I1-d, Baba–Granath / Lin–Yang's Jacobian criterion; I1-e, Shimura reciprocity,
  Jordan / González–Rotger and Elkies' model (A10, Lemma NV).

**Glue proved in Lean** (no `sorry`; axioms propext, Classical.choice, Quot.sound): A1's Gram
matrix and det 1; F1 algebra `j·Σ⁵ = 3779136·Π²`; `Sp₄(ℤ)`-invariance of the F1 ratio;
`G⁶ − 97200F² = H²`; `J(u)` finite and nonzero for `u ∉ 𝒞` and `≠ −16/27` for all rational `u`;
Elkies' `t(u) = H²/G⁶`, `t − 1 = −3(180F/G³)²`; the CM elements of `𝒪`; A7's algebraic step
`equiv_of_lyVec`. The whole file checks in about 20 s with `lake env lean`.

**Biggest obstacle.** I1-a. The rest of H uses the fibre surface `A/K` (its field, level-3
structure, conjugates). Only the canonical model, as a moduli scheme over `ℚ`, links that surface
to the analytic leaves (`Ω_A ~ Ω(τ_A)`, `j_θ(τ_A) = J(u)`). Stating it needs abelian schemes with
PEL structure, the same objects missing for I2-I5. Once I1-a exists, F1 and A7 are short glue
from I1-a + I1-b + I1-c. The explicit genus-2 model I recalled from Baba–Granath failed an exact
Igusa test and was not used.
