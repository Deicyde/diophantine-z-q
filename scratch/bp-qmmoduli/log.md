# bp-qmmoduli results log

Task: blueprint for the Shimura-curve objects of leaves R1-R3, R5 (docs/research/bp-qmmoduli.md).

## 2026-11-12

- `lake build ZInQKernel.HDecomp.Objects`: OK, 57 s (VERIFIED). Scratch files may import it.
- Mathlib v4.35 inventory (VERIFIED, ls/grep of .lake/packages/mathlib): no ample line bundles,
  no Picard scheme or dual abelian variety, no quaternion orders; present: sheaves of modules on
  schemes (`AlgebraicGeometry/Modules/Sheaf.lean`), `RingTheory/PicardGroup.lean` (Pic of a ring),
  `ProjectiveSpectrum`, group schemes (`AlgebraicGeometry/Group/{Abelian,Affine,Smooth}.lean`),
  `QuaternionAlgebra`, `ModularForms/ArithmeticSubgroups.lean`.
- `order_table.py` (sympy, VERIFIED): structure constants of 𝒪 = ℤ⟨1,i,(1+j)/2,(i+k)/2⟩ in
  B = (2,−3) are integral; x ↦ x† = μ⁻¹x̄μ preserves 𝒪; trd(x x†) = 2x0²+4x1²+18x2²−48x2x3+36x3²
  is positive definite; x†x has equal j- and k-coordinates (so x†x ∈ ker(z ↦ trd(μ⁻¹z̄)) =
  {z2 = z3}); w₂ = 1+i+j (nrd 2), w₃ = j (nrd 3), μ (nrd 6) normalize 𝒪; w₂w₃μ⁻¹ ∈ 𝒪, nrd 1;
  w₂² = 2(i+j), i+j ∈ 𝒪¹.
- `QMOrder.lean` (Mathlib only): compiles, no errors, no `sorry` (VERIFIED, `lake env lean`,
  ~15 s). Axioms of `eq_smul_E0`, `eq_pm_E0_of_principal`, `trd_mul_dag_pos`,
  `atkinLehner_relations`, `w2_normalizes`: propext, Classical.choice, Quot.sound. Contents:
  `O : Subring B`; `dag` (anti-involution, `dag_dag`, `dag_mul`, `dag_mem`, `dag_eq'`);
  `trd_mul_dag_pos` (positivity); `E0_alt`, `E0_rosati`, `E0_gram`, `gram_det`, `E0_int`;
  **`eq_smul_E0`**: every alternating ℚ-bilinear `E` on `B` with `E(ax,y) = E(x,a†y)` is `r·E₀`;
  **`eq_pm_E0_of_principal`**: Gram determinant 1 on N5's basis ⇒ `E = ±E₀`;
  `w2_normalizes`, `w3_normalizes`, `mu_normalizes`, `atkinLehner_relations`.
