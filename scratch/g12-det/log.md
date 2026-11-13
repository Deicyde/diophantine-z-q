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

## G12Weight — REDUCED (VERIFIED, compiled)

- Files: scratch/g12-det/part_weight.lean; build.sh appends it to g0-split's Split.lean (its
  `#print` lines dropped) giving Weight.lean (20.2k lines). Prerequisite: `lake build
  ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (13 s, replay).
- Copied verbatim: `G0Galois.fact_five`, `G12Weight` (part_galois.lean).
- Finding (VERIFIED, `g12Weight_concl_iff`, compiled): for `1 ≤ k`, the conclusion
  `∃ n, {n, n+1−k} = {0,−1}` is equivalent to `k = 2`.
- New named Props: `IsTwist`, `IsConj` (definitions); GLUE `TwistExists` (σ ↦ ψ(σ)ρ(σ) is a
  continuous representation), `TwistConj` (r ≅ ψ⊗ρ_g from T18 + T19), `HTConj` (HT weights
  invariant under conjugation, about `PkgI4.LocalHasHTWeights`); LEAVES `SenTwist` (Sen 1980:
  both HT of full size ⇒ `S' = S + s`, `s ∈ ℤ`), `FiniteImageHT` (finite image ⇒ HT weights all 0).
- Finding (argument, SPECULATIVE-standard): `SenTwist` needs `card S = card S' = n`; without
  full size, `HasHTWeights S` holds for non-HT reps (e.g. nilpotent Sen operator, `S = {0}`) and
  a non-integral Sen weight of `ψ` gives `S' = ∅ ≠ S + s`.
- `g12Weight_of : TwistExists → TwistConj → HTConj → SenTwist → FiniteImageHT → G12Weight`.
  Uses the given leaves R14 (HSyn.EigenformRepExists, converted to PkgI4.GaloisRep by defeq),
  R13 (PkgI4.EigenformHT) for k ≥ 2, R15 (HSyn.DeligneSerreConseq) for k = 1; T18/T19 enter only
  through `TwistConj`.
- run1 (04:32, 2m55s): fact_five missing. run2 (04:45): 0 errors; `g12Weight_concl_iff`,
  `g12Weight_of` on [propext, Classical.choice, Quot.sound].
