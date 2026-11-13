# g0-product: the glue piece `ProductExists` (G17), proved

## Verdict

**`ProductExists` is proved in Lean with no hypotheses** (VERIFIED, compiled):

```lean
theorem G0Product.productExists : G0Split.ProductExists
-- 'G0Product.productExists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The statement is copied verbatim from `scratch/g0-split/Split.lean` (l. 19570), along with the
definitions it uses: `PkgI3.AbVar`, `PkgI3.AbVar.dim`, `ZInQ.DefFaltings.AbVar`,
`ZInQ.DefFaltings.AbVar.dim` and `G0Split.IsProductOf`. A `diff` against Split.lean confirms
the copies (VERIFIED). The proof uses Mathlib v4.35.0 and nothing else: no leaf, no project
glue and no `sorry`. File: `scratch/g0-product/Product.lean`. Check it with
`lake env lean scratch/g0-product/Product.lean` (about 6 s once Mathlib is loaded).

So piece 7 of g0-split's table can be removed from `G0Split.MissingPieces`. The piece is true
and not vacuous: `P` is the actual fibre product `A ×_L Z`.

The piece's docstring says "geometric integrality of products is not in Mathlib". That is only
partly right. Mathlib 4.35 has no such lemma by name, but it has the ingredient
(`GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`, and the `IsIntegral (pullback f g)`
instances in `Mathlib/AlgebraicGeometry/Geometrically/Integral.lean`), and the composition
lemma takes 12 lines. What Mathlib really lacks is the dimension formula
`dim (X ×_K Y) = dim X + dim Y`, and the invariance of Krull dimension under integral
injective extensions. Both are proved here.

## The proof

| Lean name | statement | kind |
|---|---|---|
| `G0Product.geometricallyIntegral_comp` | if `g : X → Y` is geometrically integral, flat and universally open, and `h : Y → S` is geometrically integral and locally of finite type, then `g ≫ h` is geometrically integral | glue, proved |
| `G0Product.prodAbVar` | `A.X ⊗ Z.X` (the fibre product in `Over (Spec K)` with the product group law `GrpObj.tensorObj.instTensorObj`) is a `ZInQ.DefFaltings.AbVar K`: proper and smooth by composition and base change, geometrically integral by the lemma above | glue, proved |
| `G0Product.isProductOf_prodAbVar` | `IsProductOf (prodAbVar A Z).X A.X Z.X`, using `fst` and `snd`, which are monoid homomorphisms (Mathlib), with `lift fst snd = 𝟙` | glue, proved |
| `G0Product.DimProductOverField` (Prop) | `dim (X ×_K Y) = dim X + dim Y` for `X`, `Y` locally of finite type and quasi-compact over a field `K` (Krull dimension of the underlying spaces, in `WithBot ℕ∞`) | intermediate Prop, proved |
| `G0Product.productExists_of_dimProduct` | `DimProductOverField → ProductExists` | glue, proved |
| `G0Product.exists_le_dim_of_cover` | if open embeddings cover `X` and `X` has a chain of irreducible closed subsets of length `n`, some chart has one too (pull back along a chart meeting the smallest member) | glue, proved (topology) |
| `G0Product.Scheme.exists_le_dim_of_openCover`, `dim_le_of_isOpenImmersion`, `dim_Spec`, `dim_eq_of_iso`, `dim_pullback_Spec` | the scheme versions of these facts, and `dim (Spec R ×_K Spec S) = dim (R ⊗_K S)` (Mathlib's `pullbackSpecIso`) | glue, proved |
| `G0Product.wb_le_of_forall_nat`, `wb_add_le_of_forall` | order lemmas in `WithBot ℕ∞` | glue, proved |
| `G0Product.DimTensorFG` (Prop) | `dim (R ⊗_K S) = dim R + dim S` for finitely generated `K`-algebras | intermediate Prop, proved |
| `G0Product.dimProductOverField_of_dimTensorFG` | `DimTensorFG → DimProductOverField`: Mathlib's `affineOpenCover` on `X` and `Y`, `Scheme.Pullback.openCoverOfLeftRight`; finite type of `Spec R_i → Spec K` comes from `HasRingHomProperty.Spec_iff`. The quasi-compactness hypotheses are not used | glue, proved |
| `G0Product.ringKrullDim_eq_of_integral_injective` | an injective integral map `A → R` gives `dim R = dim A`. `≤` uses incomparability (`Ideal.IsIntegral.under_lt_under`); `≥` uses lying over and going up (`Ideal.exists_ideal_over_prime_of_isIntegral`, `Ideal.exists_ltSeries_of_hasGoingUp`) | glue, proved (commutative algebra) |
| `G0Product.tensorMap_isIntegral` | the tensor product `g ⊗ h` of integral algebra maps is integral | glue, proved |
| `G0Product.dimTensorFG` | `DimTensorFG`. Noether normalization (Mathlib's `exists_integral_inj_algHom_of_fg`) gives `K[X] → R` and `K[Y] → S`. Their tensor product `K[X] ⊗ K[Y] → R ⊗ S` is injective (`TensorProduct.map_injective_of_flat_flat`) and integral, so `dim (R ⊗ S) = dim K[X][Y] = a + b` (`MvPolynomial.algebraTensorAlgEquiv`, `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`). The cases `R = 0` and `S = 0` give `⊥ = ⊥` | glue, proved |
| `G0Product.productExists` | `G0Split.ProductExists` | **the piece, proved** |

There are no leaves. Two named intermediate Props were introduced, `DimProductOverField` and
`DimTensorFG`. Both are textbook facts and both are now proved. Standard references, given for
orientation only (theorem numbers from memory, UNVERIFIED): Stacks Project, Varieties, the
section on dimension of products, and Algebra, the section on dimension of finite type algebras
over fields; Noether normalization is Stacks 00OW (VERIFIED: Mathlib's `@[stacks 00OW]` tag).

## Remarks on the statement

- `NumberField L` is not used. The proof works over any field.
- `P.dim = A.dim + Z.dim` is proved exactly, in `WithBot ℕ∞`, so `DimFinite` is not needed.
- `P` is built from Mathlib's chosen product: `P.X = A.X ⊗ Z.X`, whose underlying scheme is
  `pullback A.X.hom Z.X.hom`. With this choice `IsProductOf` holds with `lift fst snd = 𝟙`.

## Integration check

`scratch/g0-product/mkcheck.sh` builds `SplitCheck.lean`: the whole of `Split.lean`, then
§2-§5 of `Product.lean` with `G0Split.` renamed to `HSyn.G0Split.`, then
`HSyn.glueOutputs_of_leaves_g0product`. That last theorem is `glueOutputs_of_leaves` with
`hProdE := G0Product.productExists`. **This check compiled** (VERIFIED: no errors, 2 min 54 s,
after `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`).
Both `G0Product.productExists` and `HSyn.glueOutputs_of_leaves_g0product` depend only on
`[propext, Classical.choice, Quot.sound]`. The proof therefore also compiles inside g0-split's
own context and discharges that hypothesis there. The generated file is not committed;
regenerate it with the script.

To integrate: put §2-§5 of `Product.lean` after `namespace G0Split … end G0Split` in
`part_split.lean`, with the names qualified as in `SplitCheck.lean`. Then drop the
`productExists` field of `MissingPieces` and the `hProdE` argument, passing
`G0Product.productExists` in their place. The proof needs only Mathlib, so §2-§5 could also
become a module under `ZInQKernel/HDecomp/`, stated over `Objects.lean`'s `AbVar`, which is the
same structure as `ZInQ.DefFaltings.AbVar`.
