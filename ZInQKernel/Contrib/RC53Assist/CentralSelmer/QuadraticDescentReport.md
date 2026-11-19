# Quadratic Selmer descent for the central comparison

## Result and scope

The group `S` and the map `f` of `centralSelmerComparisonOfSpecializedModel` are now constructed as the genuine objects, for `E = E_ℓ` and every integer `k` that is not a square in `ℚ`:

- `S = SelK ℓ k`, the full two-primary Selmer group `Sel_{2^∞}(E_ℓ/K)` of `E_ℓ` over `K = ℚ(√k)`;
- `f = descentToProduct ℓ hk`, the corestriction pair `x ↦ (cor x, cor ψ_* x)`, where `ψ : E_ℓ ≃ E_ℓ^{(k)}` is the twist isomorphism over `K`, followed by the existing identification of `Sel_{2^∞}(E_ℓ/ℚ) × Sel_{2^∞}(E_ℓ^{(k)}/ℚ)` with `fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)`;
- `BoundedDefects f` holds with both defects killed by `2` (`descentToProduct_boundedDefects`).

No printed theorem is assumed, no new axiom is used, and no finiteness of a Shafarevich–Tate group enters. Input (3) is therefore supplied in full. For input (2), the Selmer group `S` is supplied. The universal-coefficient map `j : (Fin r → ℚ₂/ℤ₂) →+ S` and its coordinates `eK` are not supplied, because they come from the rational Kummer complex. Input (1) is not touched.

The contribution consists of two Lean files:

- `QuadraticDescent.lean`, which imports only the existing base-zero central module and four vendored cohomology and elliptic-curve modules;
- `QuadraticDescentPlug.lean`, which imports `Comparison.lean` and `QuadraticDescent.lean`.

`QuadraticDescent.lean` elaborates by itself. Since `Comparison.lean` has no compiled form yet, the body of `QuadraticDescentPlug.lean` was checked in a scratch file that concatenates the bodies of `Comparison.lean`, `QuadraticDescent.lean` and `QuadraticDescentPlug.lean`, together with a final `example` that applies `centralSelmerComparisonOfSpecializedModel` to these objects.

## Mathematics (manuscript lines 2616–2626 and 4341–4352)

Let `E/ℚ` have `a₁ = a₃ = 0` and let `k` be a non-square. Let `r ∈ ℚˢ` with `r² = k`, let `U ⊂ G_ℚ` be the stabilizer of `r`, and let `σ ∉ U`.

1. **The field and its places.** `U` is the subgroup fixing the intermediate field `ℚ(r)`, so `U = Gal(ℚˢ/K)`. For a completion `L ∈ {ℚ_p, ℝ}` and an embedding `τ : ℚˢ → Lˢ` over `ℚ`, the decomposition group is `{h ∈ G_L : τ⁻¹ h τ ∈ U}`, which equals `Gal(Lˢ/L(τ r))`. Every place `w` of `K` arises in this way, with `K_w = L(τ r)`.
2. **The Selmer group over `K`.** `Sha(E/K)` consists of the classes in `H¹(U, E(ℚˢ))` whose restriction along every such `τ` vanishes in `H¹(Gal(Lˢ/L(τ r)), E(Lˢ))`. This is Silverman X.4 with local conditions through decomposition groups. `Sel_{2^∞}(E/K)` consists of the classes in `H¹(U, E(ℚˢ)[2^∞])` whose image lies in `Sha(E/K)`. At a complex place the decomposition group is trivial, so the condition is empty, as it should be.
3. **The twist.** `ψ(x, y) = (k x, k r y)` is a group isomorphism `E(ℚˢ) ≃ E^{(k)}(ℚˢ)`. It is equivariant for `U`, and `ψ(g P) = −g ψ(P)` for `g ∉ U`.
4. **Algebra on `H¹`.** Use the transversal `{1, σ}`. For `x ∈ H¹(U, M)`, restriction of corestriction is `x + τx`, where `τ` is conjugation by `σ`. The twisted composite `ψ⁻¹ res cor ψ` is `x − τx`. The cross terms `cor ψ res` and `cor ψ⁻¹ res` vanish: they are coboundaries of `−ψ(c(σ))`. Corestriction after restriction is the index `2`. Hence descent after ascent and ascent after descent are both multiplication by `2`.
5. **Local conditions.**
   - Restriction preserves them: a different embedding gives the same localization up to conjugation.
   - Corestriction preserves them. At a non-split place the local coset space maps bijectively to `G_ℚ/U`, and localization of a corestriction is the local corestriction. At a split place it is the sum of the localizations at the two places `τ` and `τ ∘ σ`, computed on cocycles.
   - The twist preserves them, because it commutes with the local twist by `τ(r)`.
   - The Galois action preserves them, because it moves the place `τ ∘ σ` to the place `τ`.

## Declarations

Namespace `ZInQ.Manuscript.RC53Assist.QuadraticDescent`.

**Abstract index-two setting.**
- `descentH1`, `ascentH1`.
- `ascentH1_descentH1` and `descentH1_ascentH1`: both composites are `2 •`.
- `cor_twistH1_res`: the cross terms vanish.
- `conjH1`.
- `res_cor_eq_add_conjH1`, `twist_res_cor_eq_sub_conjH1`, `conjH1_conjH1`.

**Twist.**
- `twistPointEquiv`, `twistCoeff`, `isQuadraticTwist_twistCoeff`, `intertwines_twistCoeff`.
- `pointTwist`, `twoPowerTwist`, `localTwist`.

**Field and places.**
- `galK`, `galK_eq_fixingAdjoin`, `galK_index`.
- `decomp`, `decomp_eq_fixingAdjoin`, `locK`.
- `shaStructureK`: the existing `SelmerStructure` with zero local conditions.
- `shaK`, `selmerK`, `mem_shaK`.

**Local compatibilities.**
- `res_mem_shaK`, `cor_mem_sha`.
- `pointRes_cor_of_split`, `pointRes_cor_of_not_split`.
- `twist_mem_shaK`, `twist_symm_mem_shaK`, `conjH1_mem_shaK`.

**Selmer maps.**
- `selmerDescent`, `selmerAscent`.
- `selmerAscent_selmerDescent`, `selmerDescent_selmerAscent`, `selmerDescent_boundedDefects`.
- `selmerConj`, `selmerConj_selmerConj`.

**Consistency.** `mem_selmerTwoPower_iff_res_mem_selmerK_one`: for the root `1` (that is, `K = ℚ`), the construction gives exactly `selmerTwoPower`.

**Instance for `E_ℓ`.**
- `sqrtK`, `exists_not_mem_galK`, `not_isSquare_of_neg` (so `k < 0` suffices).
- `SelK`, `quadraticDescent`, `quadraticDescent_boundedDefects`.
- `selKConj`, `selKConj_selKConj`.

**Eigenspaces.**
- `conjH1_res`: restricted classes are invariant.
- `conjH1_twistH1`: the twist anticommutes with the Galois action.
- `two_nsmul_eq_zero_of_conj_eq_self`, `exists_conj_eq_self`.
- `two_nsmul_eq_zero_of_conj_eq_neg`, `exists_conj_eq_neg`.

**Plug file.**
- `descentToProduct`, `descentToProduct_boundedDefects`.
- `ratTateSelKEquiv`: `V₂ Sel(E/K) ≅ V₂ Sel(E/ℚ) × V₂ Sel(E^{(k)}/ℚ)`.
- `finrank_ratTate_selK`: `s₂(E/K) = s₂(E/ℚ) + s₂(E^{(k)}/ℚ)`.
- `finrank_ratTate_selK_eq_one`: under `SelmerCorankOneOverK`.
- `ratTateSelKEigenspaceEquiv`: the eigenspace decomposition under the genuine `Gal(K/ℚ)` action.
- `positiveDescent_boundedDefects`, `negativeDescent_boundedDefects`: the invariant and anti-invariant parts of `Sel_{2^∞}(E_ℓ/K)` are `Sel_{2^∞}(E_ℓ/ℚ)` and `Sel_{2^∞}(E_ℓ^{(k)}/ℚ)` up to defects killed by `2`.
- `ratTateSelKEigenspaceProductEquiv`: the same rational identification through the eigenspaces.
- `centralSelmerComparisonOfQuadraticDescent`, `hcentral_of_quadraticDescent`.

## How it plugs in

```text
centralSelmerComparisonOfSpecializedModel Dm CU e1 e2 hzero hd K i eK j hj
  (descentToProduct ℓ hk) (descentToProduct_boundedDefects ℓ hk)
```

Here `S := SelK ℓ k` is fixed by the type of `j`. The packaged form is `centralSelmerComparisonOfQuadraticDescent hk Dm CU e1 e2 hzero hd K i eK j hj`. `hcentral_of_quadraticDescent … hSel` then gives the existing rank field.

## What remains open

1. **Rational Kummer comparison (input 1).** This needs the actual rational Kummer complex `K₀` with its local conditions, and the retained map `i : K₀ ⟶ scalarChangedComplex rhoT CU` with `[QuasiIsoAt i 1]`, for the actual base model `CU`. It also needs `CU.d 0 1 = 0`.
2. **Universal coefficients (rest of input 2).** This needs coordinates `eK : K₀.homology 1 ≃ₗ[ℚ₂] (Fin r → ℚ₂)` matched with the integral lattice. It also needs the map `j : (Fin r → ℚ₂/ℤ₂) →+ SelK ℓ k` from `H¹(C_K) ⊗ ℚ₂/ℤ₂` to the full Selmer group over `K`, with `BoundedDefects j`, as in lines 5305–5311. The target `SelK ℓ k` is now fixed, so `j` must land in this group.
3. **Identification of `S` with the number-field form of the Selmer group.** `SelK` realizes `G_K` as `Gal(ℚˢ/K)` inside `G_ℚ` and the completions as `L(τ√k)` inside `Lˢ`. It does not use a separate field type for `K` with separate completion types for its places. No such Selmer group exists in the library: `selmerTwoPower` is defined only for curves over `ℚ`, at the places of `ℚ`, so it cannot be applied to a curve over `K`. The construction instead follows `selmerTwoPower` and `sha` step by step. It is proved to give `selmerTwoPower` when `K = ℚ`. If a separate field-type version is ever introduced, comparing it with `SelK` is a separate step.

## Verification

- `QuadraticDescent.lean` elaborates in about 33 seconds, with the prescribed CPU affinity, six threads and priority, and with no errors or warnings.
- The scratch concatenation elaborates in about 60 seconds with no errors or warnings. It consists of the bodies of `Comparison.lean`, `QuadraticDescent.lean` and `QuadraticDescentPlug.lean`, the final `example`, and axiom reports for all 178 declarations of the two new files. The reports are recorded in `QuadraticDescentAxioms.txt`.
- Every axiom report lists a subset of `propext`, `Classical.choice` and `Quot.sound`.
- The files contain:
  - no proof placeholders;
  - no added axioms;
  - no evaluation commands;
  - no custom notation, macros or syntax;
  - no heartbeat options.
- Existing files were not edited. No version-control operation or build was run.
