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

## Step 2 (18:25) — VERIFIED (lake env lean, 0 errors)
Split of the GR glue:
- `IsShimuraModel p 𝒴 𝒜` (clauses of the leaf), `ShimuraSmoothModel p := ∃ 𝒴 𝒜, IsShimuraModel p 𝒴 𝒜`
- `VertDVRWitness E p` (DVR R ↪ E, Frac = E, 𝔪 = (p), 𝔪 ∩ ℤ[X] = pℤ[X])
- `vertGaussWitness_of_DVR : VertDVRWitness E p → VertGaussWitness E p` (compiled)
- glue `SpecialFibreDVR` (scheme theory: some stalk of a nonempty proper smooth rel-dim-1
  ℤ_(p)-scheme is a DVR with 𝔪 = (p)), glue `ModelCoordinateGlue` (comparison + coordinate)
- `modelGaussGlue_of : SpecialFibreDVR → ModelCoordinateGlue → ModelGaussGlue` (compiled;
  nonemptiness of 𝒴 from R1fp's ℚ̄-point + leaf surjectivity)
- `heckeVertWitness_of_goodReduction' (hL) (hC) (hBD) : HeckeVertWitness` (compiled)
All #print axioms [propext, Classical.choice, Quot.sound].
