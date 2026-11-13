# product-height: the glue Prop `ProductModelHeight` (P2)

Status: research note (task product-height, 2026-11-13).
- **Lean:** `scratch/product-height/ProductHeight.lean`. It imports only the kernel module
  `ZInQKernel.HDecomp.Faltings.H5Neron` (no scratch import). It compiles with
  `lake env lean scratch/product-height/ProductHeight.lean` in about 1 min. There is no `sorry`
  and no `axiom`, and all 14 `#print axioms` list only `propext`, `Classical.choice` and
  `Quot.sound`.
- **Results log:** `scratch/product-height/log.md`.
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = estimate or unchecked argument. **UNVERIFIED** =
locator from memory (no network).

## 0. Verdict

The target is `ZInQ.H5Neron.ProductModelHeight`: `h(𝒢₁) + h(𝒢₂) ≤ h(𝒢P)` for every product
`𝒢P ≅ 𝒢₁ × 𝒢₂` of smooth group models (`IsProductModel`). Its text is the same in the kernel
(`ZInQKernel/HDecomp/Faltings/H5Neron.lean`), in `scratch/h5-neron/` and in `scratch/h5-glue/`
(VERIFIED). The verbatim copy in §0 of the Lean file is checked against the kernel Prop by
`copy_iff : Copy.ProductModelHeight ↔ H5Neron.ProductModelHeight := Iff.rfl` (VERIFIED).

1. **The statement is neither false nor vacuous** (STANDARD; equality holds; §3).
2. **Analytic input of AN3 type is needed** (argued in §2, not a theorem). Two lemmas show what
   `ProductModelHeight` forces (VERIFIED, compiled):
   - `metrizable_left_of_productModelHeight` and `analyticUnif_left_of_productModelHeight`. If
     the product has one metrization and `h(𝒢₂) ≠ ⊥`, then at every `τ` the factor `𝒢₁(ℂ)_τ` has
     an analytic uniformization whose kernel is a full discrete lattice. That is the conclusion
     of `AnalyticUniformizationExists` for `𝒢₁`, obtained from the product's.
   - `le_of_productModelHeight`. Every single metrization of the product, whatever its
     uniformization, is bounded below by `h(𝒢₁) + h(𝒢₂)`.

   Neither can come from the formal transport that proved `NeronModelMinimal` (h5-glue), because
   the projections `𝒢P(ℂ)_τ → 𝒢ᵢ(ℂ)_τ` are not injective.
3. **The splitting input that h5-glue named is not needed as an input of its own.** h5-glue's
   input was "a product uniformization must split". There are two routes to P2.
   - **Route U** (g0-heightadd's route, ported here to the kernel's types) uses the two halves of
     AN3 already stated in def-faltings:
     - uniqueness, `AnalyticUniformizationUnique`;
     - existence, inside `MetrizationExists`.

     Beyond AN3 it uses only the easy product direction (`Φ₁ × Φ₂` is a uniformization of the
     product). Splitting then follows: `productMetrizationSplit_of` (VERIFIED).
   - **Route S** (new) uses only the splitting statement `ProductMetrizationSplit`. It needs no
     uniqueness, no existence and no dimension statement: `productModelHeight_of_split`
     (VERIFIED).
4. **The AN3 content of P2 is the well-definedness of def-faltings' height.** Route U needs:
   - `MetrizationHeightUnique` (new: two metrizations of one group model have the same height).
     It follows from U and `MetrizationDimUnique` (`metrizationHeightUnique_of`, VERIFIED);
   - `MetrizationExists`;
   - one product construction, `ProductMetrizationGeo`.

   The first two are what the docstrings of `MetrizedModel` and `LeafAdopt.H5` already presuppose:
   - the height does not depend on the uniformization;
   - the index set of the infimum is nonempty.

   They are not specific to products. Recommendation: classify P2 as "glue modulo AN3", i.e.
   these two well-definedness Props plus `ProductMetrizationGeo`, as in
   `productModelHeight_of_unique`.
5. **New proved pieces of `ProductMetrizationGeo`** (§4; VERIFIED):
   - `ptsEquiv : 𝒢P(ℂ)_τ ≃* 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` (as groups);
   - the product uniformization `prodUnif`, with the three algebraic clauses of
     `IsAnalyticUniformization` and kernel `Λ₁ × Λ₂` (`prodUnif_clauses`). The two analytic
     clauses are the new glue Prop `ProductUnifAnalytic`, which needs no AN3 input;
   - `prodUnif_isAnalyticUniformization` (from `ProductUnifAnalytic`).

## 1. Results (all VERIFIED: compiled, standard axioms only)

| Lean name | statement |
|---|---|
| `copy_iff` | the verbatim copy of `ProductModelHeight` (from `scratch/h5-neron/H5Neron.lean`) is the kernel Prop (`Iff.rfl`) |
| `productModelHeight_of_split` | `ProductMetrizationSplit → ProductModelHeight` |
| `metrizationHeightUnique_of` | `AnalyticUniformizationUnique → MetrizationDimUnique → MetrizationHeightUnique` |
| `productModelHeight_of_unique` | `MetrizationHeightUnique → MetrizationExists → ProductMetrization → ProductModelHeight` |
| `productModelHeight_of` | g0-heightadd's form: `U → MetrizationDimUnique → MetrizationExists → ProductMetrization → ProductModelHeight`, now on the kernel's types |
| `productModelHeight_of_geo` | the same with `ProductMetrizationGeo` (via the copied `productMetrization_of_geo`, `modelHeight_add_of`) |
| `productMetrizationSplit_of` | `MetrizationHeightUnique → MetrizationExists → ProductMetrization → ProductMetrizationSplit` (route U implies route S) |
| `le_of_productModelHeight` | P2 bounds every metrization of the product below |
| `metrizable_left/right_of_productModelHeight` | P2, a metrization of the product and `h(other factor) ≠ ⊥` give a metrization of the factor |
| `analyticUnif_left_of_productModelHeight` | ... hence an analytic uniformization of `𝒢₁(ℂ)_τ` with full discrete kernel, at every `τ` |
| `ptsProj_bijective`, `ptsEquiv` | `𝒢P(ℂ)_τ ≃* 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` for `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` with homomorphic components |
| `prodUnif_clauses` | `z ↦ (Φ₁ z₁, Φ₂ z₂)` (coordinates `Fin.append`) is a homomorphism, onto, with kernel exactly `prodLattice Λ₁ Λ₂` |
| `prodUnif_isAnalyticUniformization` | with `ProductUnifAnalytic`, it is an analytic uniformization of `𝒢P(ℂ)_τ` |
| `proj_comp_unif` | for any uniformization `Φ` of the product, `p₁ ∘ Φ` is a surjective homomorphism onto `𝒢₁(ℂ)_τ` |

Copied from g0-heightadd (`scratch/g0-heightadd/part_heightadd.lean`, `part_prod.lean`, where they
are stated over the def-faltings copy `Prefix.lean`): `ProductMetrization`, `MetrizationExists`,
`MetrizationDimUnique`, `ProductMetrizationGeo`, `modelHeight_add_of` and
`productMetrization_of_geo`. Their statements are unchanged; here they are over the kernel's
`PkgI3.AbVar`, `DefFaltings.GroupModel` and `H5Neron.IsProductModel`.

## 2. Why AN3-type input is needed (argument; SPECULATIVE in the strict sense)

The definitions (`Height.lean`, `Models.lean`, VERIFIED by reading) work as follows.
- The height `h(𝒢)` is `⨅ g, ⨅ M : MetrizedModel A L g, ⨅ (_ : M.model = 𝒢), M.hodge.modelHeight`
  in `EReal`.
- At each `τ`, a metrization's archimedean data (`periods τ`, `coeff τ`) are tied to `𝒢` only by
  `arch`. That field asks for some `Φ : ℂ^g → 𝒢(ℂ)_τ` with `IsAnalyticUniformization τ (periods τ) Φ`
  and `coeff τ (wedge f) = jacDet Φ f`.
- By Faltings' formula (`HodgeData.modelHeight_eq`), the height of a metrization depends on `Φ`
  through `|jacDet Φ s|² · covol(ker Φ)`.

A lower bound for `h(𝒢P)` therefore has to bound this quantity for **every** uniformization `Φ`
of `(𝒢₁ × 𝒢₂)(ℂ)_τ`. Here is what the definitions allow without analysis.
- The proved comparisons all move a uniformization along a bijection on complex points:
  - `NeronModelMinimal` and `HeightAntitone`, along `𝒢 → 𝒩` (h5-glue);
  - the base change `ModelHeightBaseChange`, along `ptsBaseChangeEquiv` (h5-glue).
- For a product, the maps on points are the projections `pᵢ`. They are not injective once the
  other factor has more than one point.
- So the only formal operation is `pᵢ ∘ Φ`. This is a surjective homomorphism
  (`proj_comp_unif`), and its kernel `Φ⁻¹(1 × 𝒢₂(ℂ)_τ)` is not discrete. It is not a
  uniformization.

The formal lemmas of §1 make the content of P2 explicit.
- `analyticUnif_left_of_productModelHeight`: any proof of P2 yields a uniformization of the
  factor with a discrete kernel, from one of the product.
- The known constructions of such a uniformization all use complex-analytic input:
  - either the uniformization theorem for `𝒢₁(ℂ)_τ` (AN3-existence);
  - or the splitting of `ker(p₂ ∘ Φ)`, whose identity component is a complex subspace of
    dimension `g₁`. Proving that is Lie theory of complex tori (AN3-type).
- `le_of_productModelHeight` is uniqueness-type content. It bounds every uniformization of the
  product, which is what `AnalyticUniformizationUnique` provides in route U.

An independence statement ("P2 is not provable without AN3") cannot be a theorem, since AN3 is
true. So "needed" means that no proof avoids it. The degenerate cases do not help:
- if `𝒢₂` is the trivial model, `pᵢ` is a bijection and P2 reduces to transport;
- Mathlib v4.35 cannot construct an abelian variety of positive dimension
  (g0-heightadd §3, `AbVar.zero`).

**EReal edge case** (VERIFIED). In Mathlib `⊥ + ⊤ = ⊥`, so the forcing lemmas need
`h(other factor) ≠ ⊥`. Without metrizations of `𝒢₁`, `h(𝒢₁) = ⊤`
(`height_eq_top_of_not_metrizable`).

## 3. The Props: leaf or glue, and why each is true

| name | kind | statement | why true | status |
|---|---|---|---|---|
| `H5Neron.ProductModelHeight` (P2) | glue (target) | `h(𝒢₁) + h(𝒢₂) ≤ h(𝒢P)` | equality holds (STANDARD; Faltings 1983 §1 and Deligne, Sém. Bourbaki 616 §1, locators UNVERIFIED) | **reduced**, both routes |
| `ProductMetrizationSplit` (S, new) | glue, AN3-type | every metrization `MP` of `𝒢P` yields metrizations `M₁`, `M₂` of the factors with `h(M₁)+h(M₂) ≤ h(MP)` | `g = g₁+g₂`. A holomorphic surjective homomorphism `ℂ^g → 𝒢₁(ℂ)×𝒢₂(ℂ)` with lattice kernel is `Φ₁ × Φ₂` after a linear change of coordinates (Mumford, *Abelian varieties* §1, UNVERIFIED). Then the algebra of `ProductMetrizationGeo` gives equality | unproved; implied by route U (`productMetrizationSplit_of`) |
| `MetrizationHeightUnique` (new) | glue (well-definedness of the height; AN3-uniqueness) | two metrizations of one group model, of any dimensions, have equal heights | from U and `MetrizationDimUnique` (proved). U: holomorphic homomorphisms of complex tori lift to linear maps (STANDARD) | unproved; reduced to U + DimUnique |
| `DefFaltings.AnalyticUniformizationUnique` (U) | stated in def-faltings | two uniformizations differ by `T ∈ GL_g(ℂ)` | as above. It is true for every `g`, also for `g ≠ dim A` with non-discrete kernels: `Φ = φ ∘ ℓ` with `ℓ` a surjective linear map | unproved |
| `MetrizationDimUnique` | glue (g0-heightadd) | two metrizations of one model have the same `g` | `finrank (hodgeSpace g) = 1` forces `g ∈ {0, n}` (`n = dim` of the cotangent space), and `g = 0` is excluded by surjectivity when `n ≥ 1` | unproved |
| `MetrizationExists` | glue (g0-heightadd; AN3-existence) | every group model has a metrization | `AnalyticUniformizationExists` and `HodgeLatticeTheorem` | unproved |
| `ProductMetrization` (P2a) | glue | product of metrizations, heights add | from P2a-geo (proved) | reduced |
| `ProductMetrizationGeo` (P2a-geo) | glue | product metrization with multiplicative index, coefficients and covolumes | `ω_{𝒢P} = ω₁ ⊕ ω₂`; `Φ₁ × Φ₂`; block-diagonal Jacobian | unproved. Its points part is now proved (`ptsEquiv`, `prodUnif_clauses`), and its uniformization part is reduced to `ProductUnifAnalytic` |
| `ProductUnifAnalytic` (new) | glue, no AN3 | the two analytic clauses of `IsAnalyticUniformization` for `prodUnif` | basic opens `D(Σ aᵢ ⊗ bᵢ)` of affine products `Spec(R₁ ⊗ R₂)` form a basis of `𝒢₁ ×_{𝓞_L} 𝒢₂` (products of opens do not), and `a ⊗ b` takes the value `a(Φ₁ z₁) b(Φ₂ z₂)` (EGA I 3.2.2 / Stacks 01JR, UNVERIFIED) | unproved |

No new literature leaf is introduced. U and `AnalyticUniformizationExists` state a textbook
theorem, the uniformization of complex abelian varieties (Mumford §1, UNVERIFIED), over the
project's definition `IsAnalyticUniformization`. Whether they count as leaves or as glue is for
the decomposition to decide. h5-glue recommended classifying P2 together with AN3; this note
makes that precise (§0 item 4).

## 4. What remains for `ProductMetrizationGeo` (SPECULATIVE sizes)

- `ProductUnifAnalytic`: needs Mathlib's affine fibre products (`pullbackSpecIso`) and the
  comparison of `evalAt` with the tensor decomposition. Medium.
- The lattice facts for `prodLattice Λ₁ Λ₂`: discrete, `IsZLattice`, and
  `covol = covol Λ₁ · covol Λ₂`. They need the fundamental domain `F₁ × F₂` and a
  measure-preserving `Fin (g₁+g₂) → ℂ ≃ (Fin g₁ → ℂ) × (Fin g₂ → ℂ)`. Mathlib has the pieces:
  - `ZLattice.covolume_comap`;
  - `measurePreserving_sumPiEquivProdPi`;
  - `IsAddFundamentalDomain.mk'`;
  - `ZSpan.exist_unique_vadd_mem_fundamentalDomain`.

  Small to medium; not attempted to completion.
- The Hodge-lattice half: `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}` (the stalk and cotangent space of a fibre
  product at the unit), `⋀^{top}` of a direct sum, multiplicativity of `secIndex`, and
  `jacDet (prodUnif) (p₁*f ∧ p₂*f') = jacDet Φ₁ f · jacDet Φ₂ f'` (pullback of germs along the
  projections). Large.

## 5. Integration

- The file imports only `ZInQKernel.HDecomp.Faltings.H5Neron`. It can become a kernel module
  (`ZInQKernel/HDecomp/Faltings/ProductHeight.lean`) unchanged, minus the §0 copy.
- In `scratch/h-decomposition/Leaves.lean`, `GluePieces.productModelHeight` has type
  `ZInQ.H5Neron.ProductModelHeight`. That is the Leaves.lean copy, over Leaves.lean's
  `DefFaltings.AbVar`. The proofs are generic and should paste after Leaves.lean's H5Neron
  section with `open PkgI3 (AbVar)` dropped, as g0-heightadd did (SPECULATIVE; not checked in
  this task).
- Suggested replacement of piece 5:
  `productModelHeight := productModelHeight_of_unique hH hE (productMetrization_of_geo hG)`, with
  `hH : MetrizationHeightUnique` (or `metrizationHeightUnique_of hU hD`),
  `hE : MetrizationExists` and `hG : ProductMetrizationGeo`.

## 6. Unchecked

- Locators (Mumford, Faltings 1983, Deligne 616, EGA, Stacks) are from memory: UNVERIFIED.
- §2 is an argument, not a Lean theorem.
- The sizes in §4 are SPECULATIVE.
