# alg-frob-red results log

## Setup (2026-11-13 06:40)
- src_part_tate_src.lean, src_part_bridge_src.lean, src_part_frob.lean: verbatim copies of
  origin/wip/frob-trace:scratch/frob-trace/{part_tate_src,part_bridge_src,part_frob}.lean (commit 87ed8c54).
- build.sh assembles AlgFrobRed.lean = `import ZInQKernel.HDecomp.C10.Link` + the three copies + part_red.lean.
  VERIFIED: the first 2780 lines of AlgFrobRed.lean are `cmp`-identical to frob-trace's FrobTrace.lean.
- `lake build` of the imported kernel modules: exit 0.

## Run 1-2: conjugation and finite-set split
- Statements: AlgFrobRedAt (AlgFrobRed with σ Frobenius at v itself), GoodRedCofinite (leaf candidate: good reduction
  at v ∩ L for v | p, p ∉ S), AlgFrobRedGood (local glue at one place of good reduction).
- Proved: smul_mem_nonunits, liesOver_smul, isArithFrob_conj, algFrobRed_of_at : AlgFrobRedAt → AlgFrobRed,
  algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt, algFrobRed_of_good, tateBridge35_of_good.
- Run 2: `lake env lean scratch/alg-frob-red/AlgFrobRed.lean` exit 0, no error, ~46 s; all axiom prints
  [propext, Classical.choice, Quot.sound] (VERIFIED).

## Run 3-6: local glue split (all compiled)
- New defs: Ow L v = v ∩ L, kw L v = κ(w), sf 𝒜 (special fibre, base change of the Grp along Spec κ(O) → Spec O),
  RedRel v 𝒜 e j x y (reduction relation: lift x' : Spec O_v → 𝒜 with I2 IsReductionOf's generic clause, and
  y ≫ pr₁ = Spec j ≫ Spec(residue) ≫ x').
- New Props: SmoothGeomConnIntegral (leaf candidate, textbook), ReductionMapGood (glue: valuative criterion; j and red),
  RedTorsionQbar (glue: I2-Red transported to ℚ̄ / sf / j), ReductionFrobGood (glue: NMP + Frobenius + rigidity).
- Proved: sf_isAbelianVariety (proper/smooth/geom. connected by Mathlib base-change instances + SmoothGeomConnIntegral),
  charP_kw, isUnit_cast_of_ne, algFrobRedGood_of : SmoothGeomConnIntegral → ReductionMapGood → RedTorsionQbar →
  ReductionFrobGood → AlgFrobRedGood, algFrobRed_of_pieces, tateBridge35_of_pieces.
- Run 6: exit 0, no error, no sorry; all 10 AlgFrobRedRed axiom prints [propext, Classical.choice, Quot.sound] (VERIFIED).
- Note: RedRel and the three Props need `set_option synthInstance.maxHeartbeats 400000` (Monoidal instance of
  Over.pullback along Spec(O_w → L) times out at 20000).

## Run 7-10: ReductionMapGood from the valuative criterion
- New defs: genPt, genMap (generic point map of x through e), vsq (Mathlib ValuativeCommSq for 𝒜.X.hom, R = O_v, K = ℚ̄).
- New Props: ResidueAlgClosure (glue, standard: κ(v) ≅ κ(w)‾ compatibly), RedRelMul (glue: reduction respects the group law).
- Proved: genMap_comm, exists_lift (Mathlib UniversallyClosed.eq_valuativeCriterion), lift_unique (Mathlib
  IsSeparated.valuativeCriterion), exists_redRel (pullback.lift), redRel_unique (pullback.hom_ext),
  reductionMapGood_of : ResidueAlgClosure → RedRelMul → ReductionMapGood,
  algFrobRed_of_split : GoodRedCofinite → SmoothGeomConnIntegral → ResidueAlgClosure → RedRelMul → RedTorsionQbar →
  ReductionFrobGood → FrobTrace.AlgFrobRed, tateBridge35_of_split (adds PkgI3.TateModuleFree).
- Run 10: `lake env lean scratch/alg-frob-red/AlgFrobRed.lean` exit 0, no error, no sorry; 18 AlgFrobRedRed axiom
  prints, all [propext, Classical.choice, Quot.sound] (VERIFIED).

## Run 11-13: ReductionFrobGood from FExtend + FrobMorph + rigidity
- src_Rigidity.lean: verbatim copy of scratch/mul-rigidity/Rigidity.lean (cmp-identical; G0FibreSimple.rigidityHom,
  proved from Mathlib). build.sh adds its three Mathlib imports at the top and its body after frob-trace's parts.
- New defs: sigV (σ restricted to O_v for σ ∈ D(v)). New Props: FExtend (glue: I2-NMP on the conjugate model; F̃ over
  Spec t, t ≡ Frob⁻¹ on κ(w), F̃ fixes the unit section, lift of f x = Spec(σ|O_v) ≫ x' ≫ F̃), FrobMorph (glue: the
  k-morphism β = Fr_Ā ≫ F̄ of the special fibre, fixing 0, β ∘ y = F̃ ∘ y ∘ Spec(z ↦ z^p) on k̄-points).
- Proved: residue_sigV (σ acts on κ(v) as z ↦ z^p, from IsArithFrob), reductionFrobGood_of : SmoothGeomConnIntegral →
  FExtend → FrobMorph → ReductionFrobGood (ᾱ = β is a homomorphism by rigidityHom), algFrobRed_of_fine,
  tateBridge35_of_fine.
- Run 13: exit 0, no error, no sorry; 24 axiom prints (23 AlgFrobRedRed + G0FibreSimple.rigidityHom), all
  [propext, Classical.choice, Quot.sound] (VERIFIED).

## Run 14-15: ResidueAlgClosure split
- New Props: ResidueAlgClosed (κ(v) algebraically closed, every valuation subring v of ℚ̄), ResidueAlgebraic
  (κ(v) algebraic over κ(w) for the map induced by O_w → O_v).
- Proved: instance isLocalHom_toW, residueAlgClosure_of : ResidueAlgClosed → ResidueAlgebraic → ResidueAlgClosure
  (IsAlgClosure.equiv; needs synthInstance.maxHeartbeats 400000).
- Run 15: exit 0, no error; 26 axiom prints, all standard (VERIFIED).

## Review (one model review, read-only, no human review; 2026-11-13 ~07:35)
- Verdict: all twelve Props TRUE as stated, none vacuous. Checked: FExtend's direction residue(t a)^p = residue a is the
  right one (t = σ⁻¹|O_w; the other direction would be false); FrobMorph's point formula is consistent with β over id;
  ∀ j in ReductionFrobGood/RedRelMul harmless (incompatible j: RedRel empty); RedTorsionQbar holds for every compatible j
  (O_v strictly henselian, 𝒜[m] finite étale); GoodRedCofinite, SmoothGeomConnIntegral standard (locators UNSURE).
- Remarks (no truth issue): IsFinite/Surjective F unused in FExtend, ReductionFrobGood; Bijective j redundant in
  RedTorsionQbar given compatibility; FrobMorph does not need 𝒜 abelian.

## Run 16-17: ResidueAlgClosed proved
- residueAlgClosed : ResidueAlgClosed (proved from Mathlib: lifts_and_natDegree_eq_and_monic, IsAlgClosed.exists_root,
  IsIntegrallyClosed.isIntegral_iff for the valuation subring, eval₂_hom). Run 17: exit 0, 28 prints, all standard.
- Added algFrobRed_of_final / tateBridge35_of_final (without ResidueAlgClosed); compile check in the next run.

## Run 18: ResidueAlgebraic proved
- residueAlgebraic : ResidueAlgebraic (proved from Mathlib: minimal polynomial over L, divide by a coefficient of largest
  O_w-valuation (Finset.exists_max_image), lift to O_w[X] (lifts_iff_coeff_lifts), reduce). Run 18: exit 0, 31 prints,
  all standard (VERIFIED).
- Added algFrobRed_of_main / tateBridge35_of_main (pieces: GoodRedCofinite, SmoothGeomConnIntegral, RedRelMul,
  RedTorsionQbar, FExtend, FrobMorph); compile check in the next run.

## Run 19-22: RedRelMul proved
- pb_symm_mul (inverse of the Over.map ⊣ Over.pullback bijection is multiplicative; as unram-tate's homEquiv_mul),
  pb_symm_mul' (for the group law of (Over.pullback g).mapGrp.obj G), redRelMul : RedRelMul (product of lifts; the
  generic and special-fibre passages to 𝒜 are the adjunction bijection; e.inv a homomorphism).
- Run 22: exit 0, 36 prints, all standard (VERIFIED).
- Pitfalls: inside `open scoped CategoryTheory.Obj`, IsMonHom e.inv.hom.hom is not found (instance on
  (Over.pullback g).obj 𝒜.X is Functor.monObjObj, not the mapGrp one); `rw [hmul]` gave an ill-typed motive; fixed with
  congrArg/trans chains and a `show` at the mapGrp type.
- Added algFrobRed_of_five / tateBridge35_of_five (pieces: GoodRedCofinite, SmoothGeomConnIntegral, RedTorsionQbar,
  FExtend, FrobMorph); compile check in the next run.
- Run 23 (after ./build.sh): exit 0, no error; 64 `#print axioms` lines in the file (frob-trace's, rigidityHom, and 37
  AlgFrobRedRed), all [propext, Classical.choice, Quot.sound]; `sorry` occurs only in comments (VERIFIED).
  Note: run 22's count was on a stale AlgFrobRed.lean for the last two theorems; run 23 is the check of the final file.

## Run 24-31: RedTorsionQbar from the kernel leaf I2-Red; OwDVR proved
- New: OwDVR (Prop), wOf (w = ψ⁻¹(v) for ψ : L‾ ≃ₐ[L] ℚ̄), hw_of, psiW (O_w' ≃+* O_v), psiW_toW, iotaW (Spec(j ∘ κ(ψ)) over
  Spec O_w), thetaW (I2's κ(w')-points of 𝒜 → κ(w)‾-points of sf 𝒜, via pullback.lift), thetaW_left, thetaW_symm,
  thetaHom (monoid hom), iotaW_isIso_left, thetaW_injective, thetaW_surjective, pb_mul/pb_one (+ primed forms),
  redRel_of_isReductionOf (I2's IsReductionOf ⇒ RedRel after transport), redTorsionQbar_of :
  PkgI2.ReductionTorsionBijective → OwDVR → RedTorsionQbar, algFrobRed_of_I2.
- owDVR : OwDVR (proved; adapted from neron-lg's dvrAt_center: center P = 𝔪 ∩ 𝓞_L ∋ p, 𝓞_{L,P} ≤ O_w,
  ValuationSubring.eq_of_le_of_ne_top), natCast_mem_maximalIdeal, dvrAt', toO', ringOfIntegers_mem'.
- algFrobRed_of_leaves : GoodRedCofinite → SmoothGeomConnIntegral → PkgI2.ReductionTorsionBijective → FExtend → FrobMorph
  → FrobTrace.AlgFrobRed; tateBridge35_of_leaves (adds PkgI3.TateModuleFree).
- Pitfalls: Mathlib's mapPullbackAdj is built with mkOfHomEquiv, so `homEquiv` is not definitionally the given
  toFun (pullback.lift_fst does not apply), but `homEquiv.symm v` has left `v.left ≫ fst` definitionally; define
  thetaW with pullback.lift directly. Pts (toGrp A) Ω vs A.Pt Ω: re-type with `let xw : A.Pt _ := xw0` before rw.

## Run 32-33: FExtend split
- New: tSig (t = σ⁻¹|O_w via AlgEquiv.restrictNormal and sigV σ⁻¹), tSig_residue (t induces Frob⁻¹ on κ(w), proved
  from IsArithFrob through the injective κ(w) → κ(v)), FExtendCore (glue: FExtend with t = tSig fixed, no residue
  clause), fExtend_of_core : FExtendCore → FExtend, algFrobRed_of_core, tateBridge35_of_core.
- Run 33: exit 0, no error; 79 axiom prints, all [propext, Classical.choice, Quot.sound] (VERIFIED).
- Final layout check (cmp, VERIFIED): AlgFrobRed.lean lines after the 4 imports = FrobTrace.lean minus its import line, then Rigidity.lean minus its 4 imports, byte-identical.
