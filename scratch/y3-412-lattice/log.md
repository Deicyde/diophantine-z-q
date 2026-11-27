# y3-412-lattice results log

Base: d28aef9839b8c12dcda2b24b3a22c993f4975dbf (VERIFIED, git rev-parse HEAD at start).

## Tree facts read (VERIFIED, read in the tree)
- `ShimuraCFT.rat_mem_zhat_iff` (RayClassShimura.lean) is A0 already; `inO_of_bEmb_mem`, `bEmb_mem_of_inO` give A1.
- `RayClassCFT.exists_den`, `exists_den_B` (denominators of finite adeles, via `FiniteAdeleRing.cofinite_mem_adicCompletionIntegers`).
- `RayClassCFT.classNumberOneB_proof : ClassNumberOneB` (g = bEmb γ * u, u ∈ OhatU); its proof uses I = {x | bEmb x * g ∈ OhatQ}, i.e. latticeAt g.
- `LeafQM.B` has no `Inv`; inverse is `RayClassCFT.binv γ = nrd(γ)⁻¹ • star γ` (`mul_binv`, `binv_mul`).
- `HDec.QMSplit.CNO.nrd_ne_zero : x ≠ 0 → nrd x ≠ 0` (B is a division algebra).
- `ModuliAtUnitsHP` takes Ψ : HPM → BAQˣ → _, evaluated at `toPM τ`; `ModuliAtUsedUnitsHP` takes Ψ : UpperHalfPlane → BAQˣ → _.
- bridges: `toGAf g = (x ↦ x g⁻¹)` (`app_toGAf`, rfl), `dcRelDel_iff_PM`: Deligne's class of toGAf g = kernel's class of g⁻¹.

## Part A (Y3Lattice412/Lattice.lean, Convention.lean)
- Lattice.lean: `lake env lean` clean after one fix (bounds proof: rw [bEmb_natSmul, Nat.cast_comm, mul_assoc]). COMPILED.
- Convention.lean (A5): needed `noncomputable section`; `show`/`change` to beta-reduce image lambdas. COMPILED.
- Constructions: L_g = 𝒪·binv γ from classNumberOneB_proof + A4 (with k := u ∈ OhatU, g := 1) + A2.
  Basis e_i = ofInt(Pi.single i 1) * α; lin. indep. via right mult by binv α and coordinates; span via `eq_sum_oVec` (cQ coordinates).

## Part B (Y3Lattice412/Moduli.lean)
- `IsHodgeH1PrintAt P τ L`: c : L → Path; 𝒪-clause `∀ (a : O) (b : L) (hab : a*b ∈ L), ...`.
- Needed `attribute [local instance] CloudB3W17Hodge.classicalTopology` (as in Y3HodgePrint.lean:48) for `Path (1 : P.A.Pt ℂ) 1`.
- `isHodgeH1PrintAt_O_iff` via `setOEquiv : {b | InO b} ≃ O` (identity on elements; membership defeq). COMPILED.
- `moduliAtUnitsHP_of_lattice`, `moduliAtUsedUnitsHP_of_lattice` (for Ψ restricted by toPM). COMPILED.
- Check.lean: 30 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]` (scratch/y3-412-lattice/axioms.txt). VERIFIED.
- `lake build` of Lattice, Convention, Moduli, Check: success.

## Part C / report
- docs/research/y3-412-lattice.md written. Read (VERIFIED): `finiteSubgroupQuotient_exists` is over ℚ only (AbVarQuotientFinite.lean);
  `FiniteStabilizerQuotientExists` internal unproved input; `HomLatticeCorr` leaf; `UniformizationLeafAll` leaf;
  `Y3Hodge.iota_mul_Jmat` exists (Y3HodgePrint.lean:832, needs nrd > 0).
- Class-number-one shortcut for the converse: SPECULATIVE, not attempted (B3).
