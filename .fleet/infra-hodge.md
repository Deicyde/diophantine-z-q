# infra-hodge (2026-11-13)

**Main result.** Both product Props that infra-stalks left open are now Lean theorems. Their
statements are copied verbatim and checked mechanically, there are no hypotheses, and the only
axioms are `[propext, Classical.choice, Quot.sound]`:
- `ZInQ.InfraHodge.productHodgeLattice : ZInQ.Metrization.ProductHodgeLattice` (metrization)
- `ZInQ.InfraHodge.productMetrizationOfProductUnif : ZInQ.ProductHeight.ProductMetrizationOfProductUnif`
  (product-height S-alg; field `productMetrizationOfProductUnif` of g0-assemble2's `GluePieces3`)

Also proved on the way:
- `trivialPointsCotangent : TrivialPointsCotangent` and `prodUnifDeriv : ProdUnifDeriv`: two new
  named Props, introduced here and discharged here.
- product-height's glue `ProductUnifAnalytic`: `productUnifAnalytic`.
- `productMetrizationGeo_infraHodge : ProductMetrizationGeo` (metrization's copy).
- `heightAdditivity_of_metrization_v5`: infra-stalks' `_v4` without `ProductHodgeLattice`.
- `productModelHeight_of_unifSplits : ProductUnifSplits → ProductModelHeight`, so P2's route S now
  rests on the analytic Prop S-an alone.

**What compiles.** Each check is a single file, run with `lake env lean`, with 0 errors and no
`sorry`:
- `scratch/infra-hodge/ProductHodgeLattice.lean` (52 s): verbatim metrization `Metrization.lean`,
  infra-stalks and infra-smooth-dim bodies, and the new parts `phl_*`.
- `scratch/infra-hodge/ProductSplit.lean` (25 s): imports the kernel's `H5Neron`, with verbatim
  product-height `ProductHeight.lean` and the new parts `ps_*`.
- `scratch/infra-hodge/IntegrationG0Tail.lean` (20 s): S-alg in g0-assemble2's environment
  (`import TailB`). It proves the `GluePieces3` field `productMetrizationOfProductUnif`.

The scripts `assemble.py`, `assemble_split.py` and `assemble_g0.py` regenerate the three files, and `verbatim_check.py`
prints ALL OK.

**Proof ideas.**
- Cotangent maps `cotMapAt` and the splitting `v = p₁^*i₁^*v + p₂^*i₂^*v` (from infra-stalks'
  `sub_mem_sq_pairPt`).
- `ω` is functorial for maps preserving the unit section, which gives
  `ω_P = p₁^*ω₁ ⊕ p₂^*ω₂`.
- Determinant ideals: `detIdeal (u.prod w) (W₁×W₂) = detIdeal u W₁ · detIdeal w W₂`, and indices
  of fractional ideals containing `1` multiply.
- For `g = 0`: X = 𝒢 ⊗ ℂ is Jacobson and its closed points are ℂ-points, so X is a point, and
  infra-smooth-dim's dimension = embedding dimension gives `ω = 0`.
- S-alg: the block Jacobian and a row-support count force `gᵢ(τ) = dim ωᵢ`, and the coefficient of
  `MP` on the Hodge line yields the descent of `jacDet Φᵢ`.

**What remains.** Nothing in this group. No statement changes are proposed.

**Report:** `docs/research/infra-hodge.md`. **Log:** `scratch/infra-hodge/log.md`.
