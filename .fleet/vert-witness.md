# vert-witness — fleet summary

**Result.** `HeckeRestNV.HeckeVertWitness` (the last glue Prop under `CoverModelOfHecke`) is proved
in Lean from one new leaf and two glue Props (compiled, 0 errors, standard axioms only):

`VertWitness.heckeVertWitness_of_goodReduction'' (hL : ShimuraGoodReduction)
  (hU : SpecialFibreUniformizer) (hBD : ModelCoordinateGlue) : HeckeVertWitness`

and over hecke-rest's full assembly `VertWitnessAll.coverModelOfHecke_of_goodReduction` /
`propTSAll_of_goodReduction`, which take `hL hU hBD` in place of `hV : HeckeVertWitness`.

- **Leaf `ShimuraGoodReduction`**: for p > 324, a smooth proper curve 𝒴/ℤ_(p) with the universal
  level-3 QM family (kernel's `QMFamily`, `IsFibreOf`, `QML3`), moduli bijection on ℚ̄-points,
  Hecke automorphisms over ℤ_(p), and a ℚ̄-point. Source: Kottwitz J. AMS 5 (1992) §5 / Buzzard
  Duke 87 (1997) / Morita 1981 / Carayol 1986 — locators UNVERIFIED; whether the sources state
  full level 3 at 3 | disc literally needs a human check. Reviewer: a weaker consequence, not
  vacuous.
- **Glue `SpecialFibreUniformizer`** (standard scheme theory): some stalk of a nonempty proper smooth
  relative curve over ℤ_(p) has 𝔪 = (p) with p regular. Its DVR consequence is compiled
  (`dvr_of_maximalIdeal_eq_span`, Stacks 00PD). Missing in Mathlib: "smooth over a field ⇒ reduced".
- **Glue `ModelCoordinateGlue`** (the real remaining work): generic-fibre comparison via
  `R1univProps`, and the tame quotient 𝒴/Γ' ≅ P¹_{ℤ_(p)} in the coordinate π (CM sections
  disjoint mod p by finite étale fixed loci). Reviewer: true as stated.
- Compiled commutative algebra: `VertDVRWitness → VertGaussWitness → VertLocalWitness →
  VertUnramWitness`.

**Lemma NV**: avoids a new literature leaf but needs 2-dim Abhyankar (glue from T2 + purity, or a
textbook leaf SGA 1 XIII 5), inertia at height-2 primes, and a transfer of R1rec/X6 to arbitrary
triples. Not done.

**Files**: docs/research/vert-witness.md; scratch/vert-witness/{VertMain.lean.part,
VertAllMain.lean.part, assemble.sh, VertWitness.lean (~12 s), VertAll.lean (~60-80 s),
compile_out.txt, compile_all.txt, log.md}.
