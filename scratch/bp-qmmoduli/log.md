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
