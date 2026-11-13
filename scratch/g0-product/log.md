# g0-product log

Piece: `G0Split.ProductExists` (G17), `scratch/g0-split/Split.lean` l. 19570 (branch wip/g0-split, merged).

## Step 1 (01:52 PST) — compiled
- `scratch/g0-product/Product.lean`: verbatim copies of `PkgI3.AbVar`, `PkgI3.AbVar.dim`,
  `ZInQ.DefFaltings.AbVar`, `ZInQ.DefFaltings.AbVar.dim`, `G0Split.IsProductOf`,
  `G0Split.ProductExists` (VERIFIED by diff against Split.lean; `AbVar.baseChange` omitted, unused).
- Proved (VERIFIED, compiled, axioms propext/Classical.choice/Quot.sound):
  - `G0Product.geometricallyIntegral_comp`: g geom. integral + flat + universally open, h geom.
    integral + locally finite type ⇒ g ≫ h geom. integral.
  - `G0Product.prodAbVar`: `A.X ⊗ Z.X` (fibre product, product group law) is a `DefFaltings.AbVar`.
  - `G0Product.isProductOf_prodAbVar`: `IsProductOf (prodAbVar A Z).X A.X Z.X` via fst, snd.
  - `G0Product.productExists_of_dimProduct : DimProductOverField → G0Split.ProductExists`.
- Remaining named Prop: `DimProductOverField` (textbook leaf: dim (X ×_K Y) = dim X + dim Y for
  X, Y of finite type over a field K). Reference numbers UNVERIFIED.

## Step 2 (02:00 PST) — compiled
- `G0Product.dimProductOverField_of_dimTensorFG : DimTensorFG → DimProductOverField` (VERIFIED):
  affine open covers, `Scheme.Pullback.openCoverOfLeftRight`, `pullbackSpecIso`,
  `HasRingHomProperty.Spec_iff`; topological lemma `exists_le_dim_of_cover` (chains pull back
  to a chart). QuasiCompact hypotheses unused.

## Step 3 (02:03 PST) — compiled
- `G0Product.dimTensorFG : DimTensorFG` (VERIFIED) from Mathlib: Noether normalization
  `exists_integral_inj_algHom_of_fg`, `ringKrullDim_eq_of_integral_injective` (proved here:
  incomparability + going up), `tensorMap_isIntegral` (proved here),
  `TensorProduct.map_injective_of_flat_flat`, `MvPolynomial.algebraTensorAlgEquiv`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.
- **`G0Product.productExists : G0Split.ProductExists`**, no hypotheses; axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED, `lake env lean scratch/g0-product/Product.lean`).

## Step 4 (02:08 PST) — integration check compiled
- `mkcheck.sh` → SplitCheck.lean (Split.lean + §2-§5 renamed to `HSyn.G0Split.` +
  `HSyn.glueOutputs_of_leaves_g0product`, i.e. `glueOutputs_of_leaves` with
  `hProdE := G0Product.productExists`). `lake env lean` (after
  `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`):
  no errors, 2m54s; `G0Product.productExists` and `HSyn.glueOutputs_of_leaves_g0product` depend on
  [propext, Classical.choice, Quot.sound] (VERIFIED). SplitCheck.lean not committed (regenerate).
