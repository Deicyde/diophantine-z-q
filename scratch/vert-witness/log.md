# vert-witness results log

Base: wip/vert-witness (8ec80711) + merge of origin/wip/hecke-rest (1b5849e0).
Target: `HeckeRestNV.HeckeVertWitness` (scratch/hecke-rest/NoVert.lean, verbatim).

## Plan (route GR)
1. `VertGaussWitness E p` (valuation-subring form: a valuation ring of E whose restriction to
   ℤ[X] is the Gauss valuation at p and in which p generates the maximal ideal) ⇒
   `VertLocalWitness` (hecke-rest) ⇒ `VertUnramWitness`. Commutative algebra, to compile.
2. Leaf `ShimuraGoodReduction`: smooth proper model of Y₃ over ℤ_(p), p > 324, with the
   universal family, moduli bijection on ℚ̄-points, Hecke automorphisms over ℤ_(p).
3. Glue `ModelGaussGlue`: leaf data + triple + E ⇒ `VertGaussWitness E p`.
4. Composite `heckeVertWitness_of_goodReduction`.

## Step 1 (18:05) — VERIFIED (lake env lean, 0 errors, ~12 s)
`VertWitness.lean` = NoVert.lean (lines 1-1265) + `VertMain.lean.part` (assemble.sh).
- `vertLocalWitness_of_gauss : VertGaussWitness E p → VertLocalWitness E p` (p prime)
- `vertUnramWitness_of_gauss`, `heckeVertWitness_of_gauss : HeckeVertGauss → HeckeVertWitness`
- leaf `ShimuraGoodReduction` (stated; data `ShimuraSmoothModel p` over `Zloc p = ℤ_(p)`)
- glue `ModelGaussGlue` (stated, unproved)
- `heckeVertWitness_of_goodReduction (hL : ShimuraGoodReduction) (hG : ModelGaussGlue) : HeckeVertWitness`
All #print axioms: [propext, Classical.choice, Quot.sound].
