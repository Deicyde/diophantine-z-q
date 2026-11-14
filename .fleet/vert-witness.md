# vert-witness — fleet summary

**Result.** `HeckeRestNV.HeckeVertWitness` (the last glue Prop under `CoverModelOfHecke`) is proved
in Lean (compiled, 0 errors, standard axioms only) from one new leaf, the existing bundle leaf
`R1R2fp`, one textbook statement of commutative algebra, and two glue Props:

`VertWitness.heckeVertWitness_of_leaves (hL : ShimuraGoodReduction) (hRR : R1R2fp)
  (hSR : SmoothFibreReduced) (hD : ModelCoordinate) (hB : ModelComparison) : HeckeVertWitness`

Over hecke-rest's full assembly, `VertWitnessAll.coverModelOfHecke_of_leaves` (and the coarser
`coverModelOfHecke_of_goodReduction`, `propTSAll_of_goodReduction`) replaces hecke-rest's input
`hV : HeckeVertWitness`.

- **Leaf `ShimuraGoodReduction`**: for p > 324, a smooth proper curve 𝒴/ℤ_(p) with the universal
  level-3 QM family (kernel's `QMFamily`, `IsFibreOf`, `QML3`), the moduli bijection on ℚ̄-points,
  Hecke automorphisms over ℤ_(p), and a ℚ̄-point. Sources: Kottwitz J. AMS 5 (1992) §5, Buzzard Duke
  87 (1997), Morita 1981, Carayol 1986. Locators UNVERIFIED; whether the sources state full level 3
  at 3 | disc literally needs a human check. Reviewer: a weaker consequence, not vacuous.
- **Textbook `SmoothFibreReduced`** (R → A smooth, m maximal ⇒ A/mA reduced; missing from
  Mathlib 4.35). From it, the special-fibre scheme theory is compiled: a stalk of 𝒴 is a DVR with
  uniformizer p (`specialFibreMaxIdeal_of`, `natCast_mem_nonZeroDivisors_stalk`,
  `dvr_of_maximalIdeal_eq_span`, `maximalIdeal_eq_map_of_mem_minimalPrimes`).
- **Glue `ModelCoordinate` (d)**, the main remaining work: the tame quotient 𝒴/Γ' ≅ P¹_{ℤ_(p)} in a
  coordinate ρ with R2fp's clauses; ρ has transcendental reduction at the generic points of the
  special fibre.
- **Glue `ModelComparison` (b)**: the generic fibre is ≅ Y via `R1univProps`; Möbius rigidity
  gives germ ρ ↦ X.
- Compiled algebra: `VertDVRWitness → VertGaussWitness → VertLocalWitness → VertUnramWitness`,
  `intPolyAlg_eq_eval₂`, `cmObjectsExist_of_R1R2fp`, and the wiring.
- Two read-only model reviews: leaf faithful and not vacuous; every glue Prop TRUE as stated.

**Lemma NV.** It avoids a new literature leaf but needs 2-dim Abhyankar (glue from T2 + purity, or a
textbook leaf from SGA 1 XIII 5), inertia at height-2 primes, and a transfer of R1rec/X6 to
arbitrary triples. Not done.

**Files**: docs/research/vert-witness.md; scratch/vert-witness/{VertMain.lean.part,
VertAllMain.lean.part, assemble.sh, VertWitness.lean (~12 s), VertAll.lean (~60 s),
compile_out.txt, compile_all.txt, log.md}.
