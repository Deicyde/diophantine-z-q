# pkg-I1 results log

Marks: VERIFIED (read in a source, computed, or compiled), STANDARD (published, exact reference),
SPECULATIVE. Locators from memory: UNVERIFIED.

## Step 0 (setup)
- Sources read: wk-h.md §§1-6, h-trust.md A1-A10 and F1, h-cm.md summary, N5 L377-528 (datum, degree,
  integral model), L532-543 (Igusa vector), L908-927 (theta formula); scratch/h-v14/igusa_check.py,
  scratch/rv-up/theta24.py; prereq-survey rows A2-A10, F1.
- Mathlib v4.35.0 has: `QuaternionAlgebra R c₁ c₂ c₃` (i² = c₁ + c₂ i, j² = c₃), the `GL (Fin 2) ℝ`
  action on `ℍ` (`UpperHalfPlane.glAction`), `Matrix.symplecticGroup`, `tsum`, `MeromorphicOn`.
  No Siegel upper half space, Siegel theta constants, Igusa invariants, hyperelliptic curves,
  abelian varieties with endomorphisms/polarizations, Shimura curves (VERIFIED, grep).

## Step 1 (explicit modular embedding and the analytic F1/A2 leaf; script `qm_embed.py`)
- Datum check: in ℍ[ℚ, i²=2, j²=−3], basis (1, i, (1+j)/2, (i+ij)/2), μ = 2j+ij: μ² = −6 and
  Gram(Trd(μ⁻¹ x ȳ)) = [[0,0,−1,1],[0,0,1,−2],[1,−1,0,0],[−1,2,0,0]], det 1 (VERIFIED, sympy; = N5 L410-416).
- Real embedding ι: i ↦ [[√2,0],[0,−√2]], j ↦ [[0,−3],[1,0]] (VERIFIED multiplicative on basis).
- Lattice Λ_τ = ι(𝒪)·(τ,1)ᵀ; symplectic basis e = (1, i), f' = ((1+j)/2, (i+ij)/2)·P⁻¹ with
  P = [[−1,1],[1,−2]]; Ω(τ) := F(τ)⁻¹E(τ) is symmetric with Im Ω positive definite (checked at sample
  points; E(τ)⁻¹F(τ) has negative definite imaginary part, i.e. it belongs to −E) (VERIFIED, numeric).
- j_θ(τ) := 3779136·∏_{10 even m} θ_m(Ω(τ))⁴ / (Σ θ_m(Ω(τ))⁸)⁵ (theta series truncated at |n_i| ≤ 18 or 30, 30 digits):
  - invariant under ι(x) for x = i+j (order 4), (1+j)/2 (order 6), μ (nrd 6), 1+i+j (nrd 2), j (nrd 3):
    errors ≤ 2·10⁻²⁸; under the non-torsion unit (−15/2, −11/2, −3/2, 1/2) of 𝒪¹: 2·10⁻²¹ with N = 30
    (2·10⁻⁸ with N = 18: truncation) (VERIFIED, numeric).
  - τ₋₄ = √2 + i (fixed point of ι(i+j)): ∏θ = 0, Σθ⁸ ≠ 0, so j_θ = 0.
  - τ₋₃ = i√3 (fixed point of ι((1+j)/2)): ∏θ = Σθ⁸ = 0 to working precision; |j_θ(τ₋₃ + iε)| =
    2.05·10⁶, 2.50·10⁹, 1.76·10¹² for ε = 0.1, 0.03, 0.01: growth ε⁻⁶, a pole of order 6 in τ, i.e.
    simple in the orbifold coordinate (τ−τ₋₃)⁶ (VERIFIED, numeric).
  - τ₋₂₄ = i√(9+6√2) (fixed point of ι(μ)): j_θ = −16/27 to 30 digits.
  - disc −19 point (fixed point of ι(x), x = (1/2, −1, 3/2, 0), x² − x + 5 = 0): j_θ = 81/64 = 1.265625 to
    30 digits (the value used as a cross-check in scratch/h-v14/igusa_check.py).

## Step 2 (Sp₄ transformation laws; script `theta_modular.py`)
- For Ω₀ = [[0.13+1.21i, 0.31+0.42i],[·, −0.22+1.07i]] and five generators of Sp₄(ℤ) (J, two
  translations, two diag(A, A⁻ᵀ)): Σθ⁸(MΩ) = det(CΩ+D)⁴Σθ⁸(Ω) and ∏θ²(MΩ) = det(CΩ+D)¹⁰∏θ²(Ω),
  relative errors ≤ 4·10⁻²⁵; with −det¹⁰ the error is 2.0 (VERIFIED, numeric). So the leaf
  `ThetaModularity` has the right signs and weights.

## Step 3 (I1.lean compiles: `lake env lean scratch/pkg-I1/I1.lean`, no errors, no sorry)
- Leaves (def … : Prop): `ThetaModularity`, `QMHauptmodul`.
- Proved: `gram_eq`, `gram_det` (A1), `mu_sq`, `mu_mul_muInv`, `card_evenChars` (= 10),
  `thetaRatio_invariant` (from `ThetaModularity`), `f1_algebra` (j·Σ⁵ = 3779136·Π² from LY's Igusa
  vector and LNY's theta conventions), `f1_constant`, `G6_sub_F2`, `Gu_ne_zero`, `Ju_ne_zero`
  (u ∉ 𝒞), `rat_sq_ne_three`, `quad_ne_zero`, `Hu_ne_zero`, `Ju_add` (J + 16/27 = 16H²/(27G⁶)),
  `Ju_ne_branch` (J(u) ≠ −16/27 for all u ∈ ℚ), `cm4`, `cm3`, `cm24` (i+j, (1+j)/2, μ ∈ 𝒪 with
  x² = −1, x² − x + 1 = 0, x² = −6), `elkies_t` (1 + 27J/16 = H²/G⁶), `elkies_t_sub_one`
  (27J/16 = −3(180F/G³)²).
