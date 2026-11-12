# glue-vigneras: Vignéras' local normalizer facts for A3, proved in Lean

Status: research note (task glue-vigneras, 2026-11-11). Lean: `scratch/glue-vigneras/Local.lean`
(one file, imports only `Mathlib`). Log: `scratch/glue-vigneras/log.md`.

## 1. Main result

**The local half of A3(a) is now a Lean proof, not a leaf** (VERIFIED: compiled with
`lake env lean scratch/glue-vigneras/Local.lean`, no `sorry`, `#print axioms` of the main
theorems = `[propext, Classical.choice, Quot.sound]`).

Let `B_p = B ⊗ ℚ_p = ℍ[ℚ_[p], 2, 0, -3]` (Mathlib's quaternion algebra, `i² = 2`, `j² = −3`,
`k = ij`; the same `B` as glue-repo's `GlueRepo.A1.B`) and let `𝒪_p = 𝒪 ⊗ ℤ_p` be the
`ℤ_p`-span of N5's basis `(1, i, (1+j)/2, (i+ij)/2)` (`GlueVigneras.Op p := Set.range (combp p)`,
`combp` = glue-repo's `comb` with `ℤ_[p]` coefficients). Proved:

| Lean theorem | Statement | Kind |
| --- | --- | --- |
| `mem_Op_iff_nrd_two`, `mem_Op_iff_nrd_three` | for `p = 2, 3`: `x ∈ 𝒪_p ↔ ‖nrd x‖ ≤ 1`, i.e. `𝒪_p = {x ∈ B_p : nrd x ∈ ℤ_p}` (the valuation ring of the division algebra `B_p`) | GLUE-proved |
| `normalizerOp_eq_univ` | for `p = 2, 3`: `{x ∈ B_p^× : ∀ y, y ∈ 𝒪_p ↔ x y x⁻¹ ∈ 𝒪_p} = B_p^×` | GLUE-proved |
| `mem_OpUnits_iff` | `u ∈ 𝒪_p^×` (`u, u⁻¹ ∈ 𝒪_p`) `↔ ‖nrd u‖ = 1` | GLUE-proved |
| `mem_scalOpUnits_iff` | `x ∈ ℚ_p^× 𝒪_p^× ↔ ‖nrd x‖ ∈ p^{2ℤ}` (`v_p(nrd x)` even) | GLUE-proved |
| `index_scalOpUnits` | `[B_p^× : ℚ_p^× 𝒪_p^×] = 2` (`Subgroup.index`), uniformizer `π = i` at 2 (`nrd = −2`), `π = j` at 3 (`nrd = 3`) | GLUE-proved |
| `vigneras_local` | the three facts together, for `p = 2 ∨ p = 3` | GLUE-proved |
| `unramified_normalizer` | every prime `p ≠ 2, 3`: if `x ∈ B_p^×` and `x 𝒪_p x⁻¹ ⊆ 𝒪_p` then `x ∈ ℚ_p^× 𝒪_p^×` (on N5's order itself, no splitting `B_p ≅ M₂(ℚ_p)` needed) | GLUE-proved |
| `split_normalizer_iff` | any prime `p`, any finite nonempty `n`: `x ∈ GL_n(ℚ_p)` normalizes `M_n(ℤ_p)` iff `x ∈ ℚ_p^× GL_n(ℤ_p)` | GLUE-proved |

So `[N(𝒪_p) : ℚ_p^×𝒪_p^×] = 2` at `p = 2, 3` and `= 1` at every `p ∤ 6`, all on N5's concrete
order; with the product formula of §4 this is A3(a)'s `|N/(𝔸_f^*K₀)| = 2·2 = 4`.

## 2. Published form (the leaf this replaces)

Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800 (1980), Ch. II, §1 (local
quaternion fields) and §2 (matrix algebras); theorem/lemma numbers UNVERIFIED. Also Voight,
*Quaternion Algebras*, GTM 288 (2021), Ch. 13 (§13.3, the valuation ring of a local division
quaternion algebra is its unique maximal order) and Ch. 23 (normalizers); numbers UNVERIFIED.
Statement (STANDARD):

- (R) Let `K` be a nonarchimedean local field with valuation ring `R` and `H` the quaternion
  division algebra over `K`. Then `𝒪_H = {x ∈ H : nrd x ∈ R}` is the unique maximal order of `H`;
  hence `N(𝒪_H) = H^×`, and `v ∘ nrd` induces `H^×/K^×𝒪_H^× ≅ ℤ/2ℤ`.
- (S) `N_{GL₂(K)}(M₂(R)) = K^× GL₂(R)`; every maximal order of `M₂(K)` is conjugate to `M₂(R)`.

What is proved here is the instance `K = ℚ_2, ℚ_3`, `H = B_p`, **with the extra content that
N5's lattice `𝒪_p` equals `{nrd ∈ ℤ_p}`** (so N5's `𝒪` is maximal at 2 and 3, a fact glue-repo
only cited), and (S) for every `p` and every `n` (not only `n = 2`). The published uniqueness
clause of (R) ("every order is contained in `𝒪_H`") is not needed by A3 and was not proved.

## 3. Proofs (all elementary; as formalized)

- **Anisotropic binary forms** (`norm_binary`, `norm_form2`, `norm_form3`). If `Q` is a binary
  quadratic form over `ℤ` with no nontrivial zero mod `p`, then `‖Q(x,y)‖ = max(‖x‖,‖y‖)²` on
  `ℚ_p²` (divide by the larger coordinate; the dehomogenized value is a unit because its image in
  `ZMod p` is nonzero, checked by `decide`). Used with `x² − 2y²` at 3 and `x² + xy + y²` at 2.
- **Splitting the norm form.** At 3: `nrd = (a² − 2b²) + 3(c² − 2d²)` in the coordinates
  `x = a + bi + cj + dk`. At 2: `nrd = N(n₀,n₂) − 2 N(n₁,n₃)` with `N = x² + xy + y²` in N5's basis
  coordinates `nᵢ` (`nrd_coord`, valid for every `p`). In both cases the two summands have norms
  an even and an odd power of `p` (`key`), so they cannot cancel, and `‖nrd‖ ≤ 1` forces every
  coordinate into `ℤ_p`. At 3 the passage from `(a,b,c,d)` to N5's coordinates
  `(a−c, b−d, 2c, 2d)` uses only that `2 ∈ ℤ_3`. The converse (`norm_nrd_le_one_of_mem`) holds for
  every `p` since `nrd` is an integral form in N5's coordinates.
- **Normalizer and index.** `nrd` is multiplicative, so conjugation preserves `‖nrd‖`, so every
  unit normalizes `𝒪_p = {‖nrd‖ ≤ 1}`. Units of `𝒪_p` are `{‖nrd‖ = 1}`, and `x = c·u` with
  `c = p^{−m}` whenever `‖nrd x‖ = p^{2m}`; parity of `v_p(nrd)` gives index 2 via
  `Subgroup.index_eq_two_iff`.
- **`p ∤ 6` on N5's order** (`unramified_normalizer`, certificate `scratch/glue-vigneras/cert.py`,
  output `cert.output.txt`). Let `E_kl(x)` be coordinate `l` (N5's basis) of `x eₖ x̄`; these are 16
  integral quadratic forms in N5's coordinates `nᵢ` of `x`, and they span all 10 quadratic monomials
  over `ℤ[1/6]`: `3n₀² = 2E₀₀+E₁₁+E₁₃−2E₂₀−E₃₁`, `6n₁² = −E₁₁−2E₂₀+E₃₁+E₃₃`,
  `3n₂² = 2E₀₀−E₁₁−2E₂₀−E₃₃`, `6n₃² = E₁₁+E₁₃−2E₂₀−E₃₃` (`cert0`-`cert3`, ring identities in `B_p`).
  (This is the Azumaya property `𝒪⊗𝒪^op ≅ End(𝒪)` over `ℤ[1/6]`, made explicit.) Scale `x` by its
  largest coordinate, so `x ∈ 𝒪_p` with some `‖nᵢ‖ = 1`. Since `x eₖ x̄ = nrd(x)·x eₖ x⁻¹` and
  `x eₖ x⁻¹ ∈ 𝒪_p`, `‖E_kl‖ ≤ ‖nrd x‖`; if `‖nrd x‖ < 1` the certificate gives `‖nᵢ‖ < 1` (3 and 6
  are units at `p`), a contradiction. So `nrd x ∈ ℤ_p^×` and `x⁻¹ = x̄/nrd x ∈ 𝒪_p`.
- **Split primes, matrix form** (`split_normalizer`). Scale `x` by its largest entry `x_{ki}`, so `u = x/x_{ki}`
  is integral with `u_{ki} = 1`. For every `j`, `u E_{ij} u⁻¹ ∈ M_n(ℤ_p)` and its `(k,l)` entry is
  `u_{ki}(u⁻¹)_{jl} = (u⁻¹)_{jl}`; so `u⁻¹` is integral and `u ∈ GL_n(ℤ_p)`. (No elementary divisor
  theory is needed.)

## 4. What remains for A3(a) (open glue, precisely)

1. (Done by `unramified_normalizer`; the identification `𝒪_p ≅ M₂(ℤ_p)` is not needed.)
2. **The product formula** `N/(𝔸_f^*K₀) = ∏_p N(𝒪_p)/ℚ_p^×𝒪_p^×` over the restricted product
   (Mathlib's `FiniteAdeleRing ℤ ℚ` exists, but the adelic quaternion algebra and `𝒪̂^×` are not
   set up). glue-repo §A3 notes the finite group theory `|Γ'| = |N/𝔸_f^*K₀|·|K₀/ℤ̂^*K₃|` is also
   unformalized.
3. The global index `[N_B(𝒪) : ℚ^×𝒪^×] = 4` (Atkin–Lehner group `W ≅ (ℤ/2)²`, generated by `i`
   and `j`) follows from 1, the local results here, strong approximation / class number one; A3
   itself uses only the adelic index, so this is not on the critical path.

## 5. Changes to classifications

- glue-repo A3 row (a) and pkg-I1's I1-f: the ramified-prime part and the matrix part of the
  split-prime statement move from "GLUE-open / LEAF L3" to **GLUE-proved**
  (`scratch/glue-vigneras/Local.lean`). L3 is no longer needed as a leaf, provided item 4.1 is
  proved (it is elementary) or cited as the standard maximality fact.
- The maximality of N5's `𝒪` at 2 and 3 (glue-repo A1, "cited, not formalized") is now proved
  locally: `𝒪_p = {nrd ∈ ℤ_p}` is the valuation ring, hence the unique maximal order (uniqueness
  being the published clause of (R); the inclusion `𝒪_p ⊆ {nrd ∈ ℤ_p}` and its equality are proved).
