# glue-descent log

Task: steps B1-B3, C1 of docs/research/h-trust.md (N5 = diophantine_zq.tex L632-731).
Sources read: N5 L377-412 (constants), L520-580 (K, T, L, d), L632-731 (B1-C1); h-trust B1-C1;
wk-h §§1-3; rv-h-novel log (S1.1-S2.1); prereq-survey rows B1, B2, C1.

## Step 1: ProjRep.lean (B1, C1 algebraic core) — compiles, no sorry (VERIFIED, lake env lean)
- cocycle_of_projective: T : G → Aˣ in an E-algebra, T g T h = c(g,h)•T(gh) ⇒ c 2-cocycle (trivial action).
- sign_normalization: dσ dτ = c⁴ dστ (positive reals) ⇒ dσ^{-1/4} dτ^{-1/4} c = sign(c) dστ^{-1/4}.
- sign_cocycle: sign ∘ c is a cocycle when c is.
- rho_map_mul / rhoRep: ρ(g) = β(g)⁻¹a(g)T(g) is a representation, from
  T g T h = c T(gh), a g a h c = ε a(gh), β g β h = ε β(gh).
- rho_commute: ρ commutes with every endomorphism commuting with all T g.
- rho_eq_act: ρ = Tate action where T = act, a = 1, β = 1.
- MatrixUnits2.splitEquiv / splitEquiv_intertwines / finrank_W: 2×2 matrix units commuting
  with ρ give V ≃ W × W intertwining ρ with ρ|W × ρ|W; dim V = 4 ⇒ dim W = 2.

## Step 2: Cochain.lean (B2-B3 group theory) — compiles, no sorry (VERIFIED)
- IsCochainFor ε β := β σ β τ = ε(σ,τ) β(στ); InflatedNormalized H ε := ε = 1 if an argument ∈ H.
- restrictHom: β|H is a hom; cochain_conj: β(σsσ⁻¹) = β(s) (H normal).
- kernelSubgroup K' = ker β|H; kernelSubgroup_normal; cochain_mul_kernel (β factors through G/K').
- twist, twist_sq: β·η (η hom, η² = 1) keeps dβ = ε and β² = χ.
- cochain_of_boundary_eq: β₀² = χ, dβ₀ = ε·dγ, γ² = 1 ⇒ β = β₀γ⁻¹ has β² = χ, dβ = ε.
- boundary_sq: dβ₀ is a sign when β₀² = χ is a hom.
- relindex_kernel_le / index_kernel_le: β^n = 1 on H (values in a field) ⇒ [H:K'] ≤ n,
  [G:K'] ≤ n[G:H]  (N5: [L':ℚ] ≤ 2md).
