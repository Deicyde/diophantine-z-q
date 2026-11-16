# sgr-direct results log

Base 43513d87 (leaf-fold25). Marks: VERIFIED (read/compiled/computed), STANDARD (published, reference), SPECULATIVE;
theorem numbers from memory UNVERIFIED.

## 1. Consumer map of `shimuraIntegralModelRep` (VERIFIED, read in ZInQKernel/OneProof/H)

- TailZ34 `openAddedLeaves16_of_OpenAddedLeaves17`: `shimuraGoodReductionNoGuard := SGRSplit.shimuraGoodReductionNoGuard_of_printed n.shimuraIntegralModelRep` (only use).
- TailX l.266: `shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (R1R2fp_of_rep r.r1r2) _`;
  TailX l.272: `modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' g.quotientP1Coordinate`.
- TailN l.255 / TailO l.2910: `heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5) ..`
  (= ModelGlue.heckeVertWitness_of_curveBijIso: ShimuraGoodReduction, R1R2fp, T5, ModelCoordinateResidue, CurveBijIso).
- TailK l.318: `g.heckeVertWitness` -> `propTSAll_of_pieces3` (TailI l.77) -> `HeckeRestAll.coverModelOfHecke_of_heckeRest`
  -> `CoverModelOfHecke` (NoVerticalRam of the Hecke cover E/Q(X) at every p > 324) -> `PropTSAll` (Beckmann-type
  specialization) -> `FibreUnramified` -> `fibreCoverExists_of_propTSAll'` -> `modularConstituent`.
- So the true need is `HeckeRestNV.HeckeVertWitness` (TailG l.10216): for the Hecke cover E/Q(X) (any E carrying the
  normalization chart of the R1fp/R2fp curve), every p > 324 has an unramified vertical prime; equivalently (Galois,
  compiled `heckeNoVertRam_of_witness`) `HeckeNoVertRam`. A statement about function fields: no abelian scheme.

## 2. Route analysis (summary; details in docs/research/sgr-direct.md)

- The consumer need is NoVerticalRam of the Hecke cover (a function-field statement). Good reduction of the QM surfaces at
  the points used (NOS r7a, Raynaud, SGA 7 IX, Neron, Serre-Tate CM) does not by itself give it: an inertia element at
  the Gauss prime (or at p above a point over t = J(u)) acts through 𝒪-linear automorphisms of the reduced surface,
  and excluding those needs either the integral model (the field), char-p moduli (End of the reduction), or the local
  tame-cover analysis of h-b1 Lemma NV (Abhyankar + Zariski-Nagata purity at (p, X - b)). SPECULATIVE-but-argued.
- Route NV uses existing fields only through hCM (branch fibres are CM points) and Elkies' model (elkiesX6StarPrinted);
  its local algebra uses purity in dim 2 (proved in the chain: PropTSGlue.PurityGlobalDim2 / t-purity3) and T2.
- Simplification found here: only ONE branch point (-16/27, e | 2) and ONE square root (sqrt(-(27X+16)) in Q(X6)) are
  needed for NV step 4 (h-b1 used two branch points and the W-group). VERIFIED (compiled, §3).

## 3. Lean (scratch/sgr-direct/NV.lean) — compiled, standard axioms (VERIFIED, lake env lean, 2026-11-15)

- `SGRDirect.heckeVertWitness_of_nv : R1R2fp → TorsionStructure → QMAutCard → SerreRigidity3 → ALFixedPoints →
  NVLocalInertia → RamifiedSqrtInertia → VertInertiaTrivial → HeckeBranchFibreUnram → HeckeSqrtBranch →
  HDec.HeckeRestNV.HeckeVertWitness`. `#print axioms`: propext, Classical.choice, Quot.sound.
- helpers proved: gal_fix, gal_sq, conj_fix, algebraMap_int_injective, exists_vertPrime, vert_fix,
  vertUnramWitness_of_nv.

## 4. Proofs of three of the five route-NV Props (VERIFIED: compiled, standard axioms)

- `SGRDirect.ramifiedSqrtInertia : RamifiedSqrtInertia` (scratch/sgr-direct/Ram.lean, now in the Contrib file):
  fixing group H' of the integers A' of the fixed field of σ (IsGaloisGroup.of_isScalarTower), Mathlib
  `card_inertia_eq_ramificationIdxIn` over A' (Dedekind), `ramificationIdx_tower`, and `ramificationIdx'` sSup argument.
- `SGRDirect.vertInertiaTrivial : VertInertiaTrivial` (restated: trivial vertical inertia at every vertical prime and
  degree < p ⇒ `VertUnramWitness`; Vert.lean): R₀ = ℤ[X]_(p) is a DVR (TFAE), S₀ its integral closure, separable
  residue fields from degree < p (`isSeparable_of_finrank_lt`, new lemma), card formula, chain's
  `vertUnramWitness_of_local`. Pitfall: `set R₀ := Localization.AtPrime _` hides `CommRing R₀` from instance search
  (needs `letI : CommRing R₀ := inferInstanceAs _`); `IsIntegralClosure.isFractionRing_of_finite_extension` loops
  there (use `integralClosure.isFractionRing_of_algebraic` + `IsFractionRing.comap_isAlgebraic_iff`).
- `SGRDirect.heckeBranchFibreUnram (hRR : R1R2fp) (hT : TorsionStructure) : HeckeBranchFibreUnram` (Branch.lean): the
  kernel's `residue_unramified_over_branch` on the witness, `sameTripleMor_of_mobius` + `residueImage_comp_eq_of_pt`
  to transfer, `GlueB3Unram.unramifiedAt_of_not_dvd_discr`.
- Composite `SGRDirect.heckeVertWitness_of_nvSqrt : R1R2fp → TorsionStructure → QMAutCard → SerreRigidity3 →
  ALFixedPoints → NVLocalInertia → HeckeSqrtBranch → HeckeVertWitness`. Remaining named Props: NVLocalInertia
  (local algebra, h-b1 step 3), HeckeSqrtBranch (sqrt of a(27X+16) in E, from Elkies' charts).
- `#discharges` (Discharges-output.txt): 63 open, 1853 checked, 7 discharge one (none from this file, as expected).

## 5. Constant-free square root (VERIFIED: compiled)

- `even_padicValRat_of_sq_mem`: β ∈ L (number field ⊂ Q̄, UnramifiedAt L p), β² = q ∈ ℚ^× ⇒ v_p(q) even
  (γ = den·β·p^{-k} ∈ 𝓞_L with γ² = den·num·p; P² primary; ramificationIdx' sSup argument).
- `exists_point_zero_unram`, `exists_good_sqrt`: from s² = c(27X+16) to s'² = a(27X+16) with p ∤ a (p ≥ 5), via the
  residue fields over X = 0 (R1R2fp + T5).
- `HeckeSqrtBranchAny` (∃ c ≠ 0, √(c(27X+16)) ∈ E), weaker than HeckeSqrtBranch; final composite
  `heckeVertWitness_of_nvSqrtAny : … → NVLocalInertia → HeckeSqrtBranchAny → HeckeVertWitness`.
- #discharges: 63 open, 1863 checked, 7 discharge one (none from this file).

## 6. HeckeSqrtBranchAny proved; only NVLocalInertia remains (VERIFIED: compiled, standard axioms)

- `ZInQKernel/Contrib/OneProof/SGRDirectElkies.lean` (imports SGRDirectNV and Contrib.OneProof.ElkiesX6Star):
  `exists_ringHom_ker_eq`, `eq_zero_of_forall_ringHom_qbar` (Nullstellensatz density), `gl2_inv_val`,
  `elkies_coordinate` (R1(b) into the triple + CurveSplit.curveBijIso + ShimuraGlue.Mob.good_all + orbit_iff_twist +
  MobiusGlue), `heckeSqrtBranchAny_of_elkies` (Elkies chart section pulled back to Spec B; m⁻¹(t ≠ ∞) = ⊤ via
  closed points + generization), `heckeVertWitness_of_nvElkies : R1R2fp → TorsionStructure → QMAutCard →
  SerreRigidity3 → ALFixedPoints → NVLocalInertia → ElkiesX6StarPrinted → HeckeVertWitness`.
- #discharges: 63 open, 1869 checked, 7 discharge one (none from these files).
- Fold arithmetic (deep bypass, not executed): −2 GLUE (shimuraIntegralModelRep, quotientP1Coordinate) +1 GLUE
  (nvLocalInertia) = −1.
