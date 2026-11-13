# g12-det results log

Targets (copied verbatim from scratch/g0-mod-galois): `G12Weight` (part_galois.lean),
`DetTate`, `ResQFiniteIndex` (part_det.lean).

## ResQFiniteIndex — PROVED (VERIFIED, compiled)

- File scratch/g12-det/ResQ.lean (`import Mathlib` only; copies `PkgI4.Qbar`, `PkgI4.GQ`,
  `G0Galois.resQ`, `qEmbRing`, `qEmb`, `resQ_spec`, `eq_resQ`, `ResQFiniteIndex` verbatim).
- `G0Galois.resQFiniteIndex : ResQFiniteIndex`. Proof: `qEmbRing K : ℚ̄ → K̄` is bijective
  (`IsAlgClosed.ringHom_bijective_of_isIntegral`, `K̄` integral over `ℚ`); `K' := image of K in ℚ̄`
  has `[K':ℚ] = [K:ℚ]`; `fixingSubgroup K' ≤ range (resQ K)` (conjugate `σ` by `qEquiv`, then
  `eq_resQ`); index of `fixingSubgroup K'` = `[K':ℚ] ≠ 0` (`finrank_eq_fixingSubgroup_index`);
  `Subgroup.finiteIndex_of_le`.
- run1 (04:14, 2m37s): 0 errors. run2 (04:19): 0 errors; axioms [propext, Classical.choice,
  Quot.sound].

## DetTate — REDUCED to `TateGSp` (glue, from T9/T26) + `Darboux` (linear algebra) (VERIFIED, compiled)

- File scratch/g12-det/DetTate.lean (`import Mathlib`, `import ZInQKernel.HDecomp.Objects`).
  Objects' PkgI3 section = Split.lean L2418-2764 up to whitespace (VERIFIED, `diff`), so the
  copied `DetTate` is the same statement. Copied verbatim: `PkgI4.Qbar`, `GQ`,
  `GlueI3.repBaseChange`, `resQ`, `qEmbRing`, `resQ_spec`, `Vb`, `tate`, `toRingEquivQ`, `cycQ`,
  `DetTate`.
- New named Props: `Darboux` (symplectic basis, Gram matrix = Mathlib `Matrix.J`), `SympSimDet`
  (det of a similitude with multiplier `c ≠ 0` of a nondegenerate alternating form in dim `2n`
  is `cⁿ`), `TateGSp` (nondegenerate alternating `B` on `V_ℓ(A)`, `dim = 2g`, multiplier the
  cyclotomic character of `G_K` on `K̄`).
- Proved: `sympSimDet_of_darboux : Darboux → SympSimDet` (via `M·diag(1,c⁻¹) ∈ Sp`, Mathlib
  `SymplecticGroup.det_eq_one`); `cyc_eq_of_intertwines` (cyclotomic characters agree along an
  intertwining ring hom), `cycQ_resQ`; `detTate_of : TateGSp → SympSimDet → DetTate`
  (`LinearMap.det_baseChange`); `detTate_of_darboux`.
- run1 (04:23): 4 errors (`ᵀ` not open, namespace `SymplecticGroup`, `unique` goal shape,
  cast). run2: 1 error (final field_simp). run3 (04:26): 0 errors; all four theorems on
  [propext, Classical.choice, Quot.sound].
- Note (VERIFIED by reading scratch/weil-pairing): weil-pairing proved only
  `det ρ_ℓ(σ)² = χ^{rank}`; the sign (Pfaffian) is what `Darboux` + `det_eq_one` supply.
