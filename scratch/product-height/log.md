# product-height results log

## Run 1 (2026-11-13, from 04:08 PST)

- Target: `ZInQ.H5Neron.ProductModelHeight` (kernel `ZInQKernel/HDecomp/Faltings/H5Neron.lean` l.220);
  text identical in `scratch/h5-neron/H5Neron.lean` l.215, `Neron.lean` l.225,
  `scratch/h5-glue/Additivity.lean` l.285, `H5Final.lean` l.2264 (VERIFIED, grep).
- `lake build ZInQKernel.HDecomp.Faltings.H5Neron`: success (9053 jobs) (VERIFIED).
- `ProductHeight.lean` compile 1 (55 s): all theorems compile with only the standard axioms except the
  §0 copy (`tensorGen` took `j` explicitly: the line `variable {j P}` of the original was missing). Fixed.
- `ProductHeight.lean` compile 2: 0 errors; all nine `#print axioms` list only `propext`,
  `Classical.choice`, `Quot.sound` (VERIFIED). `copy_iff` (`Iff.rfl`) confirms the verbatim copy is
  the kernel Prop.
- Compile 3 (with §4 `analyticUnif_left_of_productModelHeight` and §5 points/product
  uniformization): 0 errors, 0 warnings in output; all 14 `#print axioms` standard (VERIFIED).
  New proved: `ptsEquiv` (`𝒢P(ℂ)_τ ≃* 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ`), `prodUnif_clauses` (hom, kernel
  `prodLattice Λ₁ Λ₂`, onto), `prodUnif_isAnalyticUniformization` (from glue `ProductUnifAnalytic`),
  `proj_comp_unif`.
- Docstring of `ProductUnifAnalytic` corrected (products of opens are not a basis of the Zariski
  topology of a fibre product; basic opens `D(Σ aᵢ ⊗ bᵢ)` of affine products are).
- Independent read-only model review (general-purpose agent) of `ProductHeight.lean`. Findings:
  all Props true; `ProductUnifAnalytic` docstring correct. **The §4 necessity claim (P2 needs
  AN3-type input) is unsound**: the product's own uniformization `Φ` splits by elementary
  analysis. `K₁ = ker(p₁∘Φ)` is closed, because `p₁ x = 1` is Zariski-closed, the unit section of
  a separated scheme being a closed immersion. Its identity component `W₂` is a complex subspace,
  by the identity theorem and clause 5. `W₁ + W₂ = ℂ^g` (Baire) and `W₁ ∩ W₂ ⊆ Λ`, so
  `W₁ ∩ W₂ = 0`. Then `Φ ∘ T = Φ₁ × Φ₂`. `ProductMetrizationSplit` is nearly a restatement of P2
  (attained infima).
  Author re-check of each step: agrees (kernel of `Φ|_{W₁}` is `Λ ∩ W₁` since
  `W₁ ∩ K₁ ⊆ K₁ ∩ K₂ = Λ`; `Λ = Λ∩W₁ ⊕ Λ∩W₂`). Verdict changed: AN3 not needed.
- Compile 4-6 (§6: `isAnalyticUniformization_comp`, `recoordM`, `recoordM_modelHeight`,
  glue `ProductUnifSplits` (S-an), `ProductMetrizationOfProductUnif` (S-alg),
  `productMetrizationSplit_of_splits`, `productModelHeight_of_splits`): fixes were a
  `DifferentiableOn.comp` term, a namespace rename (`recoordM`) and an explicit `@hA` for the
  `IsMonHom` instances across `recoordM`. Final: 0 errors, 18/18 `#print axioms` standard
  (VERIFIED). Docstrings of §1, §4 and the header corrected (no AN3 claim).
- Second model-review pass (same agent, on §6): `ProductUnifSplits` and
  `ProductMetrizationOfProductUnif` true as formalized for every `g` (incl. `g = 0`), non-vacuous,
  no AN3 hidden; `gᵢ(τ) = dᵢ` derivable in S-alg from `finrank_eq_one` + block Jacobian; the
  nonzero-wedge fact is algebraic. Nits (Zariski-closedness wording, two omitted ingredients in
  S-an, finrank/cotangent splitting in S-alg) applied to the docstrings.
- **Integration check** (`build_integrated.sh`): `LeavesIntegrated.lean` = `scratch/h-decomposition/
  Leaves.lean` + §1-§6 (no §0 copy, `open PkgI3 (AbVar)` dropped) + an `example` closing
  Leaves.lean's `ZInQ.H5Neron.ProductModelHeight` (the type of `GluePieces.productModelHeight`,
  Leaves.lean l.33739) by `productModelHeight_of_splits hS hA`. `lake env lean`: 0 errors,
  8 min 29 s; `productModelHeight_of_splits`, `productModelHeight_of_geo` standard axioms only
  (VERIFIED). The generated 34k-line file is not committed (regenerate with the script).
- `Lattice.lean` (Mathlib only; standalone): `discreteTopology_prod`, `instIsZLatticeProd`,
  `exists_unique_add_mem`, `isAddFundamentalDomain_prod`, `covolume_prod`
  (`covol(Λ₁ × Λ₂, μ₁.prod μ₂) = covol Λ₁ · covol Λ₂`), `splitCL_measurePreserving`,
  `prodLattice_eq_comap`, `prodLattice_facts` (product lattice discrete, full, covolume
  multiplicative). Compile iterations: name `discreteTopology_iff_isOpen_singleton`, `hs.le`
  instead of `▸`, `piCongrLeft` symm by `show` + `Equiv.piCongrLeft_symm_apply`, explicit
  `Measure.prod.instIsAddHaarMeasure` for the product volume. Final: 0 errors, 2/2 axioms
  standard (VERIFIED).
- Merged into `ProductHeight.lean` as §5b (binder `ι` renamed `κ`: `ι` is a token under the
  file's opens), plus `prodUnif_fullLattice` (from `ProductUnifAnalytic`: the product of
  full-lattice uniformizations is one, with multiplicative covolume). Compile: 0 errors,
  21/21 `#print axioms` standard (VERIFIED).
- Integration check re-run on the final `ProductHeight.lean` (with §5b): 0 errors, 8 min 14 s;
  `productModelHeight_of_splits`, `productModelHeight_of_geo` standard axioms (VERIFIED).
- §6b (pieces of S-an): `dom_comp` (rfl), `evalAt_comp` (`s(f∘p) = (f* s)(p)`; closed by
  `congr 1` after the `dif_pos` rewrites), `analyticClauses_comp`, `analyticClauses_precomp`,
  `proj_analyticClauses` (clauses 4, 5 for `z ↦ p₁(Φ(ℓ z))`, any linear `ℓ`). Compile: 0 errors,
  23/23 `#print axioms` standard (VERIFIED); 4 deprecation warnings (`dif_pos`/`dif_neg`).
