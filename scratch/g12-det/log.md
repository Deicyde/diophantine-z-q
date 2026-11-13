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

## Darboux — PROVED (VERIFIED, compiled); DetTate now rests on TateGSp alone

- scratch/g12-det/Darboux.lean (`import Mathlib`): `G0Galois.darboux : Darboux`. Induction on
  `n`: hyperbolic pair `B e f = 1`, `H = span{e,f}`, `IsCompl H H^⊥`
  (`isCompl_orthogonal_of_restrict_nondegenerate`), `B|H^⊥` nondegenerate alternating of
  dimension `2n` (`finrank_orthogonal`); family `Sum.elim (Fin.cons f w_l) (Fin.cons e w_r)` with
  Gram `J`; independence from `J² = −1`; `basisOfLinearIndependentOfCardEqFinrank'` (the unprimed
  one needs `Nonempty`, fails at `n = 0`). runs 04:45-04:48: 3 fix rounds; final 0 errors, axioms
  standard.
- Same proof appended to DetTate.lean; `detTate_of_tateGSp : TateGSp → DetTate`. run4 (04:49):
  0 errors; `sympSimDet_of_darboux`, `cycQ_resQ`, `detTate_of`, `detTate_of_darboux`, `darboux`,
  `detTate_of_tateGSp` all on [propext, Classical.choice, Quot.sound].

## TateGSp and DetTate from leaves (VERIFIED, compiled)

- DetTate.lean additions: `TatePairingZl` (alternating `ℤ_ℓ`-form on `T_ℓ A`, trivial left kernel,
  cyclotomic multiplier), `tateGSp_of_zl : TatePairingZl → PkgI3.TateModuleFree → TateGSp`
  (Gram matrix of a basis of `T_ℓ`, mapped to `ℚ_ℓ`, in the base-changed basis
  `Algebra.TensorProduct.basis`; `LinearMap.toMatrix_baseChange`; alternating from skew Gram +
  char 0), `detTate_of_zl`. run (04:55): 0 errors, axioms standard.
- DetLeaves.lean (build_det.sh) = part_wp.lean (WeilPairing.lean §1-§9 verbatim, L6-1149, minus
  `twist_finite_four` L644-675, which needs GlueAssembly) + DetTate.lean body + part_leaves.lean:
  `tatePairingZl_of_leaves : T09_SymmIsogenyExists → IsogenyQuasiInverse → DivisiblePoints →
  TatePairingZl` and `detTate_of_leaves : … → PkgI3.TateModuleFree → DetTate`.
  run1 (04:56): 1 error (`Gal K` vs `Field.absoluteGaloisGroup K` in a rewrite); run2 (04:58):
  0 errors, 0 sorry; both on [propext, Classical.choice, Quot.sound].

## TwistExists, TwistConj PROVED; G12Weight from HTConj + two leaves (VERIFIED, compiled)

- part_twist.lean (appended to Weight.lean by build.sh): copies `FrobeniusDenseQ`,
  `frobeniusDenseQ_of`, `eq_of_eq_on_arithFrob`, `continuous_mat` verbatim from part_det.lean;
  `scalarU`, `twistHom`, `twistExists : TwistExists` (continuity via `Units.continuous_iff`);
  `invariant_of_irreducible`, `isSemisimple_of_irreducible`, `isSemisimple_twist`,
  `twistConj_of : HSyn.FrobeniusDense → HSyn.BrauerNesbitt → TwistConj`;
  `g12Weight_of_HT : HTConj → SenTwist → FiniteImageHT → G12Weight` (T18, T19 are hypotheses of
  `G12Weight` itself).
- run (05:01): 2 errors (`bot_le` shape; a `simp only` no-op). run (05:05-05:08): 0 errors,
  0 sorry; `g12Weight_concl_iff`, `g12Weight_of`, `twistExists`, `twistConj_of`,
  `g12Weight_of_HT` on [propext, Classical.choice, Quot.sound].

## HTConj REDUCED to HTExtend (VERIFIED, compiled in the fast environment)

- part_htconj.lean: `HTExtend` (GLUE: a model over finite `E ⊆ ℚ̄_p` with weights `S` gives a
  model over any finite `E' ⊇ E` with weights `S`); `finrank_htSpace_conj` (conjugating a model by
  `P ∈ GL_n(E)` gives `ℚ_p`-isomorphic `htSpace`s, `φ ↦ φ ∘ P`); `htConj_of : HTExtend → HTConj`
  (`E' = E ⊔ ℚ_p(entries of P, P⁻¹)`, finite by `finiteDimensional_adjoin`; lift `P` to
  `GL_n(E')`; conjugate the `E'`-model).
- Fast environment HTFast.lean = Split.lean L1-4727 (through `end PkgI4Sec`) + part_htdefs.lean
  (copies of `IsConj`, `HTConj`) + part_htconj.lean; 1m10s per run. run1 (05:10): 4 errors;
  run2 (05:13): 0 errors, 0 sorry; `finrank_htSpace_conj`, `htConj_of` standard axioms.
- Model review (subagent, read-only, no Lean; 05:12): all new Props TRUE and non-vacuous; no
  serious issue. Notes: `htMult`'s division is exact (htSpace is an `E`-space by precomposition);
  `SympSimDet` holds even without `c ≠ 0`; `G12Weight` witness: `V_5` of a non-CM elliptic curve
  over ℚ with `ψ = 1`.
- run (05:13-05:16) Weight.lean with part_htconj + part_final: 0 errors, 0 sorry; `g12Weight_of_htExtend : HTExtend → SenTwist → FiniteImageHT → G12Weight` and all earlier theorems on standard axioms.

## HTExtend PROVED (VERIFIED, compiled in the fast environment)

- part_htextend.lean: for fields `E ⊆ E'` (`IsScalarTower ℚ_p E E'`, basis `b` of `E'/E` of size
  `m`): `jk`, `ck` (coordinate maps), `htSpaceExtendEquiv : htSpace(ρ_{E'}) ≃ₗ (Fin m → htSpace(ρ_E))`,
  `htMult_extend` (`(m·d)/(m·e) = d/e`, `finrank_finsupp`, tower law), `htExtend : HTExtend`
  (`Algebra E E'` from `IntermediateField.inclusion`).
- runs 05:16-05:22 (HTFast, ~1 min each): 4 fix rounds (p implicit in `jk`, `LinearMap.sum_apply`,
  `include b`, universe of `Fin m` vs `Type*` → `Type`, `card_fin`); final: 0 errors, 0 sorry;
  `htExtend` on [propext, Classical.choice, Quot.sound].
- run (05:23-05:26) Weight.lean full: 0 errors, 0 sorry; `g12Weight_of_senTwist : SenTwist → FiniteImageHT → G12Weight` and the nine other G0Galois theorems on [propext, Classical.choice, Quot.sound].

## Integration check against g0-mod-galois (VERIFIED, compiled)

- build_det.sh now derives DetLeaves.lean from DetTate.lean directly (part_dt.lean removed);
  rerun (05:26): 0 errors, 0 sorry, `tatePairingZl_of_leaves`, `detTate_of_leaves` standard.
- build_int.py → Integrate.lean (23.3k lines) = scratch/g0-mod-galois/ModGalois.lean (its
  `#print`s dropped) + the NEW parts of g12-det only (all copied definitions removed, so
  `G12Weight`, `DetTate`, `ResQFiniteIndex`, `GaloisPieces` are g0-mod-galois's own constants;
  weil-pairing §1-§9 compiled over Split.lean's PkgI3) + part_integrate.lean:
  `galoisPieces_of : BurnsideAbsIrred → R14Det → G9Glue → G10Glue → SenTwist → FiniteImageHT →
  T09_SymmIsogenyExists → IsogenyQuasiInverse → DivisiblePoints → PkgI3.TateModuleFree →
  GaloisPieces` and `g8_g12_of_leaves'` (G8-G12 from the leaf bundles with glue `G9Glue`,
  `G10Glue` only; T26 = the bundle's `t26`).
- run (05:27-05:31): 0 errors, 0 sorry; both on [propext, Classical.choice, Quot.sound].
