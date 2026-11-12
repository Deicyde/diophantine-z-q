# glue-vigneras results log

## Local.lean (lake env lean scratch/glue-vigneras/Local.lean)
- 23:47 chunk 1 COMPILES (no errors): `norm_binary` (anisotropic binary form: ‖Q x y‖ = max(‖x‖,‖y‖)²),
  `norm_form3` (ℚ_3: ‖a²−2b²‖ = max²), `norm_form2` (ℚ_2: ‖a²+ab+b²‖ = max²). VERIFIED (compiled).
- 23:48 chunk 2 COMPILES: `Bp p = ℍ[ℚ_[p],2,0,-3]`, `combp`, `Op p = Set.range combp` (ℤ_p-span of N5's basis
  (1, i, (1+j)/2, (i+ij)/2)), `coord`, `mem_Op_iff_coord`, `nrd` (= (x x̄).re), `nrd_eq`, `mul_star_eq`, `nrd_mul`,
  `nrd_smul`, `nrd_coord` (nrd = N(n0,n2) − 2 N(n1,n3), N = x²+xy+y²), `norm_nrd_le_one_of_mem` (any p),
  `key` (valuation parity: ‖u‖ = M1², ‖v‖ = M2²/p, ‖u+v‖ ≤ 1 ⇒ M1, M2 ≤ 1).
- 23:48 chunk 3 COMPILES: `mem_Op_iff_nrd_two`, `mem_Op_iff_nrd_three`: 𝒪_p = {x ∈ B_p : ‖nrd x‖ ≤ 1} for p = 2, 3.
- 23:50 chunk 4 COMPILES: `OpUnits`, `normalizerOp`, `scalOpUnits`, `mem_OpUnits_iff` (u ∈ 𝒪_p^× ↔ ‖nrd u‖ = 1),
  `normalizerOp_eq_univ` (N(𝒪_p) = B_p^×), `mem_scalOpUnits_iff` (x ∈ ℚ_p^×𝒪_p^× ↔ ‖nrd x‖ ∈ p^{2ℤ}),
  `scalOpUnitsSubgroup`, `exists_pi` (π = i at 2, nrd −2; π = j at 3, nrd 3), `index_scalOpUnits` (index = 2),
  `vigneras_local` (summary). `#print axioms vigneras_local` = [propext, Classical.choice, Quot.sound]. VERIFIED.
- 23:55 chunk 5 COMPILES: split primes, matrix form, any prime p, any nonempty finite n:
  `IntMat`, `mul_single_mul_apply`, `intMat_single`, `split_normalizer` (x M_n(ℤ_p) x⁻¹ ⊆ M_n(ℤ_p) ⇒ x ∈ ℚ_p^× GL_n(ℤ_p);
  proof: scale by the largest entry x_{ki}, conjugate E_{ij}: (u E_ij u⁻¹)_{kl} = (u⁻¹)_{jl}), `intMat_mul`,
  `split_normalizer_converse`, `split_normalizer_iff`. VERIFIED (compiled).
- 00:00 `cert.py` (pure Python, Fractions; output `cert.output.txt`): the 16 coordinates E_kl of x e_k x̄ in N5's
  basis are integer quadratic forms spanning all 10 quadratic monomials (rank 10); certificates
  3n0² = 2E00+E11+E13−2E20−E31, 6n1² = −E11−2E20+E31+E33, 3n2² = 2E00−E11−2E20−E33, 6n3² = E11+E13−2E20−E33. VERIFIED (computed).
- 00:01 chunk 6 COMPILES: `ek`, `Ent`, `cert0..cert3` (ring identities in B_p, any p), `eq_of_coord`, `coord_smul`,
  `star_mem`, `small_*`, `norm_int_eq_one`, `unramified_normalizer`: for p ≠ 2, 3, x ∈ B_p^× with x 𝒪_p x⁻¹ ⊆ 𝒪_p
  ⇒ x ∈ ℚ_p^×𝒪_p^× (directly on N5's order, no splitting B_p ≅ M₂). Axioms: [propext, Classical.choice, Quot.sound]. VERIFIED.
- 00:03 cert.py extended: all 10 monomials n_a n_b have certificates with denominators dividing 6 (VERIFIED, computed;
  cert.output.txt "mon" lines). `gen_global.py` generates `Eint` and `cert_ab` for Global.lean.
- 00:04 Global.lean COMPILES (no sorry): over ℚ, `B`, `comb`, `O`, `coordQ`, `nrd`, `nrdInt`, `Eint`, `cert_ab` (10),
  `Eint_eq`, `nrd_dvd_Eint`, `nrd_dvd_six`: x = comb n ∈ 𝒪 primitive (∑ sₖnₖ = 1) normalizing 𝒪 ⇒ nrd x ∣ 6.
  Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- 00:09 Global.lean COMPILES (no sorry): `combMul`, `comb_mul`, `O_mul`, `O_star`, `N` (Subgroup Bˣ: x𝒪x⁻¹ = 𝒪),
  `OUnits`, `S` (= ℚ^×𝒪^×), `iU`, `jU`, `iU_mem`, `jU_mem`, `primitive_scaling` (x = c·comb a, a primitive, Bezout),
  `vhom`, `nrdU`, `φ : N →* (ℤ/2)²` (v₂, v₃ of nrd mod 2), `divisors_six`, `phi_eq_one_iff` (ker φ = ℚ^×𝒪^×),
  `phi_surjective` (images of i, j), `global_index`: (∀ x : N, x ∈ ker φ ↔ x ∈ ℚ^×𝒪^×) ∧ (ker φ).index = 4.
  `#print axioms global_index` = [propext, Classical.choice, Quot.sound]. VERIFIED.
- 00:10 `S_subset_N`, `normalizer_index_four` COMPILE; axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
