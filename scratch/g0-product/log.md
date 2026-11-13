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
