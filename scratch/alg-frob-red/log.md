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
