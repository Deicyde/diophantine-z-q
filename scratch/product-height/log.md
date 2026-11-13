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
