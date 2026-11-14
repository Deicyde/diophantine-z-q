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
