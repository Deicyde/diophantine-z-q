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

## Step 3: Constants.lean (B2-B3 constants, repo definitions) — compiles, no sorry (VERIFIED)
Imports ZInQKernel.Compiler.Precision.HeightConstant (heightD_eq, heightE0_eq; kernel never evaluates D).
- ramSet S u := S ∪ primeFactors(contactSupport S u)   (N5's T).
- prod_odd_le: ∏_{p∈T, p≠2}(p-1) ≤ R^R · M_S(u) for S primes ≤ R, R ≥ 1.
- degree_le_QM: S primes, D ≤ R, max S ≤ R, 10¹² ≤ R, d ≤ D, m ≤ 2∏_{p∈T,p≠2}(p-1)
  ⇒ (2md : ℝ) ≤ heightQ R · M_S(u).   (N5 L713: [L':ℚ] ≤ 2md ≤ 4DR^RM ≤ QM.)
  Uses only 1 ≤ D (heightD_pos), 10 ≤ E₀ (ten_le_heightE0).

## Step 4: Chi.lean (B2's χ) — compiles, no sorry; #print axioms exists_chi: propext, Classical.choice, Quot.sound (VERIFIED)
- exists_odd_char: n > 2 ⇒ ∃ χ : DirichletCharacter ℂ n, χ(-1) = -1 (MulChar duality).
- orderOf_dvd_totient, orderOf_prod_dvd.
- exists_chi: T primes, T₋ ⊆ T, χ = ∏_{p∈T₋} changeLevel(χ_p) at level N = ∏ lev p (lev 2 = 4):
  each χ_p odd; every prime factor of N lies in T; orderOf χ ≤ 2∏_{p∈T,p≠2}(p-1).

## Step 5: B2Glue.lean (deduction of B2 from its inputs) — compiles, no sorry (VERIFIED)
Over any topological group G, index set ι, groups Gv v with continuous r v : Gv v →* G, comm group U;
"continuous into discrete" = IsLocallyConstant. IsSignCocycle η (loc. const, η² = 1, cocycle);
SignCob η (η = dγ, γ loc. const sign cochain).
- exists_beta: hasse (sign cocycle locally SignCob at all v ⇒ SignCob) + local_two (H²(Gv,±1) has
  ≤ 2 classes) + ε sign cocycle + χ : G →* U with loc. const pointwise sqrt β₀ + agree
  (∀ v, SignCob(ε∘r_v) ↔ SignCob(dβ₀∘r_v)) ⇒ ∃ β loc. const, β² = χ, β σ β τ = ε(σ,τ) β(στ).
- signCob_dB_iff: SignCob(dβ₀) ↔ ψ has a loc. const square-root character (β₀² = ψ).
- Cochain.lean additions: twist_kills_inertia (unique nontrivial quadratic char of each I_v,
  η ramified exactly where β is ⇒ βη = 1 on every I_v); inertia_le_kernel (I_v ≤ K').

## Step 6: B2 leaves stated over Mathlib objects (B2Glue.lean, namespace GlueDescent.B2Q) — elaborate (VERIFIED)
GQ = Field.absoluteGaloisGroup ℚ, GQp p = Field.absoluteGaloisGroup ℚ_[p], resp p = absoluteGaloisGroup.map
(algebraMap ℚ ℚ_[p]) (continuous), cyc N = modularCyclotomicCharacter on ℚ̄, galChar χ = χ.toUnitHom ∘ cyc N.
- LeafHasse (L-B2a): sign 2-cocycle of G_ℚ locally a coboundary at every finite p ⇒ coboundary.
- LeafLocalTwo (L-B2b): H²(G_{ℚ_p}, ±1) has ≤ 2 classes.
- LeafSqrtCrit (L-B2c): χ mod N = p^k N', u ≡ -1 mod p^k, ≡ 1 mod N' ⇒ (χ|G_{ℚ_p} has a loc. const
  square-root character ↔ χ(u) = 1).
- LeafUnramified (L-B2d): ε inflated from Gal(L/ℚ), L finite Galois, every prime of 𝓞 L over p has
  ramificationIdx 1 ⇒ ε|G_{ℚ_p} is a coboundary.

## Step 7: B2Assembly.lean — B2 over G_ℚ from the four leaves — compiles, no sorry;
## #print axioms b2_of_leaves: propext, Classical.choice, Quot.sound (VERIFIED)
Out-of-tree build: OUT=scratch/glue-descent/.lake/out (gitignored);
lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean -o $OUT/GlueDescent/{Chi,B2Glue}.olean scratch/glue-descent/{Chi,B2Glue}.lean"
then the same LEAN_PATH for B2Assembly.lean.
- B2Glue additions: cyc_isLocallyConstant (cyclotomic character continuous: invariant under the open
  fixing subgroup of ℚ(μ_N)), galChar_isLocallyConstant, sqrtU / sqrtU_sq.
- exists_crt_unit: u ∈ (ℤ/N)^× with u ≡ -1 mod p^{v_p N}, ≡ 1 mod N/p^{v_p N}.
- chi_toUnitHom_crt: χ(u_p) = if p ∈ T₋ then -1 else 1.
- b2_of_leaves: LeafHasse, LeafLocalTwo, LeafSqrtCrit, LeafUnramified; L ⊂ ℚ̄ finite Galois, ε sign
  cocycle inflated from Gal(L/ℚ), L unramified outside finite prime set T ⇒ ∃ N, χ mod N, β : G_ℚ → ℂ^×
  loc. const with primes of N in T, orderOf χ ≤ 2∏_{p∈T,p≠2}(p-1), β² = galChar χ, dβ = ε.

## Step 8: B3Assembly.lean — B3 over G_ℚ — compiles, no sorry; axioms of b3_of_leaves,
## b3_degree_le_QM: propext, Classical.choice, Quot.sound (VERIFIED)
- inflatedNormalized_of: ε inflated from Gal(L/ℚ), cocycle, ε(1,1) = 1 ⇒ ε = 1 when an argument is in G_L.
- b3_of_leaves: hypotheses of b2_of_leaves + ε(1,1) = 1 ⇒ χ, β as in B2 and L' = fixedField(ker β|G_L):
  L ≤ L', FiniteDimensional, IsGalois ℚ L', G_{L'} = {σ ∈ G_L | β σ = 1}, β constant on G_{L'}-cosets,
  finrank L' ≤ 2·orderOf χ·finrank L. (Mathlib: finrank_eq_fixingSubgroup_index for ℚ̄/ℚ,
  InfiniteGalois.fixingSubgroup_fixedField, isOpen_iff_finite, normal_iff_isGalois.)
- b3_degree_le_QM: + admissible (S,R), finrank L ≤ heightD, T = ramSet S u ⇒ (finrank L' : ℝ) ≤ heightQ R · M_S(u).
- Not formalized: L' unramified outside T (needs inertia subgroups of G_ℚ; group core = twist_kills_inertia).
