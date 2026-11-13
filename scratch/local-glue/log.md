# local-glue results log

## Step 1 (2026-11-13 06:53-07:00 PST): setup and statements
- Merged origin/wip/local-data (fast-forward of its commits onto 322303a2).
- Target: `G15Ram.LocalGlue p Tm a β L` (scratch/local-data/part_local.lean l.933), with
  `TorsionFieldWild`, `TateWildTrivialL`, `TateWildTrivial`, `BetaUpper`, `Lv`, `G7Clauses`, `U0`.
  Copy: `scratch/local-glue/LocalGlue.lean` = whole `scratch/local-data/LocalData.lean` (verbatim,
  `cat`) + `part_glue.lean` (new), assembled by `build.sh`.
- Finding G1 (logical, VERIFIED by reading): `LocalGlue` is a predicate on arbitrary
  `(Tm, a, β, L)`; it fails for `Tm = 0` at `p > D` (to be compiled: `not_localGlue_zero`).
  It is also not implied by `G7Out ∧ G8Out ∧ G7Clauses`: these tie `a·Tm` to an abelian variety
  only on `G_K` (`K = L'`), and nothing ties `K` to `L` (SPECULATIVE example: `L = ℚ`, `A = E²_K`,
  `K/ℚ` cyclic of degree `p` inside `ℚ(ζ_{p²})`, `Tm = ψ ⊗ tate(E²)` with `ψ` of order `p`,
  conductor `p²`, trivial on `G_K`; then `a·Tm(σ) = ψ(σ) ≠ 1` on some wild `σ`).
- Finding G2 (VERIFIED, read scratch/g0-mod-field/ModField.lean l.611-631): g0-mod-field's
  `G7Data` has the kernel field clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`, and `DescentDatum`
  has `A` over `L` with `m_σ` = Galois action and `a = 1` on `G_L`. g0-mod-galois's `G7Out` keeps
  only `Tm = tate`, `a = 1` on `G_K`. So at odd `p` the kernel-field clause puts wild inertia of
  `G_L` inside `G_K` (β is tame there), and the abelian-variety content is on `A/K` only.
- `lake build` of the 11 imported kernel modules started (HDecomp not prebuilt here).

## Step 2 (07:00-07:03 PST): reduction compiled
- `lake build` of the 11 imported modules: ok (9075 jobs, fast: shared artifacts).
- `scratch/local-glue/LocalGlue.lean` (build.sh: verbatim LocalData.lean + part_glue.lean).
  `lake env lean scratch/local-glue/LocalGlue.lean`: exit 0, 0 errors, no sorry, ~20 s;
  `#print axioms` [propext, Classical.choice, Quot.sound] for all 7 printed (compile.out).
- Proved (VERIFIED):
  * `not_localGlue_zero (hp : D < p) L : ¬ LocalGlue (Tm := 0) (a := 1) (β := 1) L` (G1).
  * `fixSet_Lv_iff : σ ∈ fixSet (Lv L) ↔ ∀ x ∈ L, decomp p σ x = x`.
  * `beta_wild_of_clauses (p ≠ 2) : G7Clauses β ε L → σ ∈ wildSet → decomp σ fixes L →
    β (decomp σ) = 1`.
  * `aTm_eq_one_of_kerWild`, and the main reduction
    `localGlue_of_g7 : G7Out A ℓ Tm c ε a β u → G7Clauses β ε L → KerWild K β L →
     (7 ≤ p → TateWildK A ℓ) → (p ≤ 5 → TateWildKE A ℓ β L) → (p = 2 → BetaUpper β (Lv L) U0)
     → LocalGlue p Tm a β L`.
  * `tate_eq_one_of_torsFix`: σ fixes every ℓⁿ-torsion point of A(K̄) ⇒ `tate A ℓ σ = 1`;
    `tateWildK_of_torsFixWild`, `tateWildKE_of_torsFixWildE`.
- New named Props (glue): `KerWild`, `TateWildK`, `TateWildKE`, `TorsFixWild`, `TorsFixWildE`.
- Pitfall: after `open CategoryTheory`, `ι` is a token (rcases pattern fails); renamed.

## Step 3 (07:03-07:07 PST): packs
- §7: `G0ModNewform.G8LocalPack` copied verbatim from scratch/local-data/tail_part.lean;
  new `G7LocalPackK ℓ r P` (G7Out, G8Out, G7Clauses, KerWild, and at p ∈ P: TorsFixWild for
  p ≥ 7, TorsFixWildE for p ≤ 5, BetaUpper for p = 2).
- Proved (VERIFIED, compiled, axioms standard): `g8LocalPack_of_K : G7LocalPackK ℓ r P →
  G8LocalPack ℓ r P`; `g15RamG_of_packK : G7LocalPackK 5 D.r5 (· ≠ 5) → G7LocalPackK 3 D.r3
  (· = 5) → G11Out T D.r5 → G11Out T D.r3 → G15RamG D u`.
- Compile: exit 0, 0 errors, no sorry, 9 printed declarations all standard axioms.

## Step 4 (07:07-07:12 PST): TorsFixWild at p ≥ 7 from I2-Tors and R6 at the place
- §8 of part_glue.lean. Proved (VERIFIED, compiled, axioms standard):
  * `iterate_card_GL_fix`: φ : G →* G injective, S mult.-closed, φ(S) ⊆ S, S ≅ (ℤ/q)ⁿ as groups
    ⇒ φ^[|GLₙ(𝔽_q)|] = id on S (via `Matrix.GeneralLinearGroup.toLin`, `pow_card_eq_one'`).
  * `card_GL4_three : Nat.card (GL (Fin 4) (ZMod 3)) = 24261120` (`Matrix.card_GL_field`);
    `card_GL4_seven = 2400·2394·2352·2058`; `coprime_card_GL4_three` (p prime, 7 ≤ p, p ≠ 13);
    `coprime_card_GL4_seven` (13).
  * `fixed_of_unipSq_of_iterate'` (D2's core, PkgI3 points); `galAct_inv_galAct`,
    `galAct_injective`.
  * `torsGL_of_leaf : ObjBridge.TorsionStructure → A.dim = 2 → 0 < m → TorsGL A m`
    (the I2-Tors leaf applies to `ObjBridge.toGrp A` and its torsion set is defeq to PkgI3's).
  * `fix_torsion_of_coprime`, `torsFixWild_of_raynaud (ℓ ≠ p) (7 ≤ p) : WildIter A →
    TorsGL A 3 → TorsGL A 7 → RaynaudPlace A 3 → RaynaudPlace A 7 → TorsFixWild A ℓ`,
    `tateWildK_of_leaves` (with I2-Tors and dim A = 2).
- New named glue: `WildIter p A` (bridge: points over finite extensions + wild ⇒ p-power period),
  `RaynaudPlace p A m` (R6 at the place of embP, needs the DVR/valuation-ring bridge and base
  change to K(A[m])). `TorsGL` is proved from the leaf.
- Pitfall: with `open MonObj`, `one_mul` resolves to `MonObj.one_mul`; use `_root_.one_mul`.
  `galHom_mul` rewrites need `σ : AlgebraicClosure K ≃ₐ[K] _`, not `Field.absoluteGaloisGroup K`.
- Compile: exit 0, 0 errors, no sorry; all 14 printed declarations standard axioms.

## Step 5 (07:12-07:21 PST): WildIter from PtFinite; file split
- Files: part_glue.lean (§6 reduction, §7 torsion), part_pack.lean (§8 packs, with the verbatim
  `G8LocalPack` between `-- BEGIN/END verbatim copy` markers), galois_block.lean (verbatim
  part_galois.lean l.40-58: `qEmbRing`, `qEmb`, `resQ_spec`; made by mk_galois_block.sh).
- Proved (VERIFIED, compiled, axioms standard): `galAct_galAct`, `galAct_iterate`;
  `qEmbRing_surjective` (ℚ̄ → K̄ onto: `IsAlgClosed.ringHom_bijective_of_isIntegral`,
  `RingHom.IsIntegral.tower_top`, `Algebra.IsIntegral.trans K`); `pow_fix_mono`;
  `wild_pow_fix_elem` (wild σ', x ∈ K̄ ⇒ ∃ a, σ'^{p^a} x = x; via exists_pow_fix_of_wild on the
  normal closure of ℚ_p(embP y), decomp_spec, resQ_spec); `wild_pow_fix_field` (finite F/K, basis);
  `wildIter_of_ptFinite : PtFinite A → WildIter A`; `tateWildK_of_leaves'` (I2-Tors, dim A = 2,
  PtFinite, RaynaudPlace A 3, RaynaudPlace A 7 ⇒ TateWildK, p ≥ 7, p ≠ ℓ).
- New named glue: `PtFinite A` (K̄-points defined over finite extensions; Mathlib-level).
- Compile: `lake env lean scratch/local-glue/LocalGlue.lean` exit 0, 0 errors, no sorry;
  45 `#print axioms` lines (27 from LocalData.lean + 18 new), all [propext, Classical.choice,
  Quot.sound].
- `lake build` of local-data's Tail.lean imports: ok (9561 jobs).

## Step 6 (07:21-07:23 PST): tail
- `scratch/local-glue/TailK.lean` (build_tail.sh: verbatim scratch/local-data/Tail.lean +
  galois_block.lean + part_glue.lean + part_pack.lean minus its verbatim G8LocalPack copy +
  tail_glue.lean).
- Proved (VERIFIED): `G0ModNewform.modularConstituent_tail_K`: g0-mod-newform's tail (G13-G16)
  with hypothesis `∃ D, G12Spec D ∧ G14TraceCompat D ∧ G7LocalPackK 5 D.r5 (· ≠ 5) ∧
  G7LocalPackK 3 D.r3 (· = 5) ∧ G11Out T D.r5 ∧ G11Out T D.r3`.
- Compile: `lake env lean scratch/local-glue/TailK.lean` exit 0, 0 errors, no sorry, ~50 s;
  axioms of `modularConstituent_tail_K` [propext, Classical.choice, Quot.sound]
  (tail_compile.out).

## Step 7 (07:23-07:30 PST): leaf-and-bridge packs
- Proved (VERIFIED, compiled, axioms standard): `torsFixWildE_of_odd` (odd p: G7Clauses +
  `TorsFixWildOdd` (new glue def: TorsFixWildE without the β clause) ⇒ TorsFixWildE);
  `G0ModNewform.G7LocalPackR` (new def: G7Out, G8Out, G7Clauses, KerWild, PtFinite A, and at
  p ∈ P: RaynaudPlace A 3 ∧ RaynaudPlace A 7 if p ≥ 7, TorsFixWildOdd if 3 ≤ p ≤ 5,
  TorsFixWildE ∧ BetaUpper if p = 2); `g7LocalPackK_of_R (hTors : ObjBridge.TorsionStructure)
  (hPℓ : ∀ p, P p → p ≠ ℓ) : G7LocalPackR ℓ r P → G7LocalPackK ℓ r P`; `g15RamG_of_packR`;
  in TailK.lean `modularConstituent_tail_R` (tail with I2-Tors and G7LocalPackR).
- Compile: LocalGlue.lean exit 0, no sorry, all printed axioms standard; TailK.lean exit 0,
  no sorry, `modularConstituent_tail_R` axioms [propext, Classical.choice, Quot.sound].

## Step 8 (07:25-07:31 PST): BetaUpper at p = 2 without T16
- Finding G6 (VERIFIED, compiled): `BetaUpper β L_v U₀` follows from G7's clauses and the
  smaller Prop `BetaTwist2 β L` (some `M ⊇ L_v`, `[M:ℚ_p] ≤ 4[L_v:ℚ_p]`, with `β = 1` on wild
  inertia of `G_M`), using only the degree-based break bound already proved in g15-ram
  (`UpperBreakFix` from `hilbertSerre_of_model (ladicDVRModel_of_Zp ladicDVRModelZp)`, i.e. T20 +
  T21 via t-different) and `upperWild`. No T16, no D3 (`(U^{e+1})⁴ = U^{3e+1}`), no Herbrand ψ.
  Math (SPECULATIVE-free, STANDARD): β⁴ = χ² is unramified at 2 (2-part of χ = character mod 4);
  an unramified 4th root η of β⁴|G_{L_v} exists (G_{L_v}/I procyclic); M = kernel field of βη⁻¹.
- Proved (VERIFIED): `betaUpper_of_twist : G7Clauses β ε L → BetaTwist2 β L →
  BetaUpper β (Lv L) U0`; `localGlue_of_g7_twist` (main reduction with BetaTwist2);
  `G7LocalPackR` now asks for `BetaTwist2` at p = 2 (g7LocalPackK_of_R uses betaUpper_of_twist).
- Compile: LocalGlue.lean exit 0, no sorry, all printed axioms standard; TailK.lean exit 0, no
  sorry, tail_K and tail_R axioms standard.

## Step 9 (07:31-07:38 PST): PtFinite proved
- New part `part_ptfinite.lean` (§7b); build.sh/build_tail.sh prepend
  `import Mathlib.AlgebraicGeometry.AffineTransitionLimit` (Mathlib oleans prebuilt).
- Proved (VERIFIED, compiled, axioms standard): `FIdx K` (finite subextensions of K̄/K, directed),
  `fRingDiag`, `fRingCocone`, `fRingCoconeIsColimit` (K̄ = colim F; adapted from
  scratch/morph-descend's `ringCoconeIsColimit`), `fSpecDiag`, `fSpecCone`, `fSpecConeIsLimit`
  (Spec K̄ = lim Spec F, `isLimitOfPreserves Scheme.Spec` + `IsLimit.equivOfNatIsoOfIso`),
  **`ptFinite (A : PkgI3.AbVar K) : PtFinite A`** (Mathlib's
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, Stacks 01ZC; smooth ⇒ LFP),
  `wildIter A : WildIter A`, `tateWildK_of_raynaud (ℓ ≠ p) (7 ≤ p) : ObjBridge.TorsionStructure
  → A.dim = 2 → RaynaudPlace A 3 → RaynaudPlace A 7 → TateWildK A ℓ`.
- `G7LocalPackR` no longer has the `PtFinite A` clause.
- Pitfall: `rw [← Spec.map_comp]` fails when an object is `(D).obj F` vs `Spec (of F)`; use
  `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) ?_)` and
  `(Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)`.
- Compile: LocalGlue.lean exit 0, no sorry, 52 printed declarations all standard axioms;
  TailK.lean exit 0, no sorry, tail_K/tail_R standard axioms.

## Step 10 (07:38-07:45 PST): vacuity fix for RaynaudPlace at m = p
- Finding G7 (logical): `G7LocalPackR` (step 7) required `RaynaudPlace A 7` at every `p ≥ 7`,
  including `p = 7`, where `m = 7 = p` is not invertible and Raynaud's criterion does not apply
  (the statement can fail), which could make the pack unsatisfiable. Fixed: `RaynaudPlace A 3` is
  required only for `p ≠ 13` and `RaynaudPlace A 7` only for `p = 13`; `torsFixWild_of_raynaud`,
  `tateWildK_of_leaves`, `tateWildK_of_leaves'`, `tateWildK_of_raynaud` now take
  `(hR3 : p ≠ 13 → RaynaudPlace A 3) (hR7 : p = 13 → RaynaudPlace A 7)`. Docstring of
  `RaynaudPlace` says: claimed only for `m ≥ 3` prime to `p`.
- Compile: LocalGlue.lean exit 0, no sorry, all standard; TailK.lean exit 0, no sorry, standard.

## Step 11 (07:45-07:55 PST): verbatim checks, report
- Verbatim check (VERIFIED, python substring test): scratch/local-data/LocalData.lean occurs whole in
  LocalGlue.lean; scratch/local-data/Tail.lean whole in TailK.lean; part_galois.lean l.40-58 in
  LocalGlue.lean; the G8LocalPack block of part_pack.lean (between markers) occurs in
  scratch/local-data/tail_part.lean.
- docs/research/local-glue.md rewritten with the final state (verdict, main result, remaining
  Props, findings G1-G7).

## Step 12 (07:45-07:52 PST): R6 at the place, rational case
- `neron_block.lean` (mk_neron_block.sh): verbatim slices of scratch/neron-lg/NeronLG.lean on
  origin/wip/neron-lg (l.207-215 `dvrAt` + DVR instance, l.225-236 `ringOfIntegers_mem`, `toO`,
  `toO_coe`, l.1406-1472 `center'`, `dvrAt_center'`, `isDiscreteValuationRing_of_ne_top`).
  Extra import `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`.
- `part_raynaud.lean` (§7c). Proved (VERIFIED, compiled, axioms standard): `normVS` (valuation
  subring {‖f x‖ ≤ 1}), `eK : ℚ̄ ≃+* K̄`, `ιbar`, `wK`, `OK`, `wK_comap`, `OK_ne_top`,
  `OK_dvr` (instance), `isUnit_natCast_OK` (p ∤ n), `ιbar_apply` (ιbar ∘ σ' = σ ∘ ιbar),
  `norm_wild_eq`, **`isInertia_of_wild`** (wild σ' over decomp σ ∈ PkgI2.IsInertia (wK p K)),
  **`raynaudPlace_rational (hR6 : ObjBridge.RaynaudCriterion) (A) (3 ≤ m) (p ∤ m)
  (A[m] K-rational) : RaynaudPlace A m`** — the leaf R6 applies at the place of embP; PkgI2's
  galAct/UnipSq/torsion on `ObjBridge.toGrp A` are defeq to PkgI3's (VERIFIED by the compile).
- Compile: exit 0, no sorry, all printed axioms standard.

## Step 13 (07:52-08:00 PST): RaynaudPlace proved from R6 + I2-Tors (general case)
- `bc_block.lean` (mk_bc_block.sh): verbatim scratch/unram-tate/BCPoints.lean l.14-142
  (origin/wip/unram-tate): `UnramTate.bcPt`, `bcPt_galAct`, `trPt`, `trPt_galAct`.
- Proved (VERIFIED, compiled, axioms standard): `normVS_ne_top`, `isUnit_natCast_normVS`,
  `isInertia_of_wild_gen` (f ∘ τ = σ ∘ f, σ wild ⇒ IsInertia (normVS f) τ), `torsStab`,
  `exists_fin_le_torsStab` (G_{F'} ⊆ stab A[m], F' finite: ptFinite + I2-Tors finiteness),
  **`raynaudPlace_of_R6 (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
  (A) (dim A = 2) (3 ≤ m) (p ∤ m) : RaynaudPlace A m`** — R6 applied over F = fixedField(stab A[m])
  (closed since open: `Subgroup.isOpen_mono`, `IntermediateField.fixingSubgroup_isOpen`,
  `InfiniteGalois.fixingSubgroup_fixedField`), a number field; Ω = AlgebraicClosure F ≅ K̄
  (`IsAlgClosure.equiv`); A_F = A.baseChange F with points via bcPt/trPt; valuation rings
  normVS (ιbar ∘ ψ); σ₁ = ψ⁻¹σ'ψ inertial by `isInertia_of_wild_gen`; A_F[m] F-rational since
  G_F = stab A[m].
  **`tateWildK_of_R6`**: TateWildK A ℓ at p ≥ 7, p ≠ ℓ from R6 + I2-Tors + dim A = 2 alone.
- `G7LocalPackR` has no clause at p ≥ 7 any more; `g7LocalPackK_of_R`, `g15RamG_of_packR`,
  `modularConstituent_tail_R` take `hR6 : ObjBridge.RaynaudCriterion` and `hTors`.
- Compile: LocalGlue.lean exit 0, no sorry, 56 printed declarations all standard axioms;
  TailK.lean exit 0, no sorry, tail_K/tail_R standard axioms.
- (08:00-08:02) Proved (VERIFIED): `localGlue_of_leaves (hR6) (hTors) (p ≠ ℓ) : G7Out → G7Clauses →
  KerWild → (p ≤ 5 → TateWildKE) → (p = 2 → BetaTwist2) → LocalGlue p Tm a β L`.
  Compile: exit 0, no sorry, 57 printed declarations all standard axioms.

## Step 14 (08:03-08:19 PST): p <= 5 from a descent Prop
- New: `resq_block.lean` (mk_resq_block.sh): verbatim scratch/g0-assemble/parts/75_modfield.lean
  l.786 `numberField_of_fd`, l.895-985 `actQ`, `actK`, `resQ_comm'`, `resQ_range` (namespace `RQ`,
  `GaloisCopy.resQ` -> `G0Galois.resQ`, `IF` -> `IntermediateField ℚ PkgI4.Qbar`).
- New part `part_descent.lean` (§7d). New glue Prop `DescentPts A L` (IsGalois ℚ L, a model
  `A₀ : AbVar L`, dim 2, `φ : A₀(L̄) ≃* A(K̄)` with `φ ∘ σ₀ = σ' ∘ φ` when `resQ L σ₀ = resQ K σ'`).
- Proved (VERIFIED, compiled, axioms standard): `index_torsStab_le` ([G_K : Stab(A[q])] ≤ |GL₄(𝔽_q)|,
  via a hom `G_K →* (𝔽_q⁴ ≃ₗ 𝔽_q⁴)`), `resQ_injective'`, **`torsFix_of_descent`** (R6 + I2-Tors +
  DescentPts, prime q ≥ 3, q ≠ p, finite M ⊇ L_v ⟹ ∃ E ⊇ M, [E:ℚ_p] ≤ |GL₄(𝔽_q)|[M:ℚ_p], wild σ ∈ G_E
  fixes A(K̄)[ℓⁿ]; E = fixedField(decomp⁻¹(resQ_L Stab) ∩ G_M), degree = index by Mathlib's
  `IntermediateField.finrank_eq_fixingSubgroup_index`), `card_GL4_five` (= G₀),
  `torsFixWildOdd_of_descent` (every p ≠ ℓ), `torsFixWildE_of_twist` (p ≠ 3, from BetaTwist2),
  `tateWildKE_of_descent`, **`localGlue_of_descent`**: LocalGlue from R6, I2-Tors, `KerWild`,
  `p ≤ 5 → DescentPts A L`, `p = 2 → BetaTwist2 β L` (with `[FiniteDimensional ℚ L]`).
- Compile: LocalGlue.lean exit 0, 0 errors, no sorry, 63 printed declarations all
  [propext, Classical.choice, Quot.sound] (compile.out).
- Remaining glue for LocalGlue: KerWild, DescentPts (p ≤ 5), BetaTwist2 (p = 2). No other Prop.

## Step 15 (08:19-08:24 PST): descent pack and tail
- `part_pack.lean`: new `G7LocalPackD ℓ r P` (G7Out, G8Out, G7Clauses, KerWild, FiniteDimensional ℚ L,
  and at p ∈ P: `p ≤ 5 → DescentPts A L`, `p = 2 → BetaTwist2 β L`); proved (VERIFIED)
  `g8LocalPack_of_D (hR6) (hTors) (p ≠ ℓ on P)`, `g15RamG_of_packD`.
- `tail_glue.lean`: proved (VERIFIED) `modularConstituent_tail_D` (G13-G16 on G7LocalPackD + R6 + I2-Tors).
- Compile: LocalGlue.lean exit 0, no sorry, 65 printed declarations standard axioms; TailK.lean exit 0,
  no sorry, all printed axioms standard (incl. modularConstituent_tail_D).

## Step 16 (08:24-08:40 PST): BetaTwist2 reduced to a textbook Prop; Beta4Inertia proved
- New part `part_twist.lean` (§7e). New Props: `Beta4Inertia β L` (β⁴ = 1 on G_{L_v} ∩ inertiaSet;
  glue) and `UnramRoots p ℓ` (GLUE, textbook: a character of G_F trivial on an open subgroup and on
  inertia has an unramified continuous 4th root; Serre, Local Fields III §5 / IV §2, UNVERIFIED).
- Proved (VERIFIED, compiled, axioms standard):
  `betaTwist2_of_roots (hC) (UnramRoots) (Beta4Inertia) : BetaTwist2` (M = fixed field of
  {σ ∈ G_{L_v} : β = η}, kernel of β/η : G_{L_v} → μ₄, index ≤ card(rootsOfUnity 4) ≤ 4);
  `inertia_fix_prime_to_p`, `sq_fix_four` (σ² fixes μ₄), `chiLevel_dvd_four_mul_odd`,
  `decomp_sq_fix_root`, `cyc_decomp_sq_inertia` (p = 2: cyc_N(decomp σ²) = 1 for inertia σ),
  **`beta4Inertia_of_clauses (p = 2) (hC : G7Clauses) : Beta4Inertia`**,
  `betaTwist2_of_unramRoots`, **`localGlue_of_unramRoots`** (LocalGlue from R6, I2-Tors,
  UnramRoots, KerWild, p ≤ 5 → DescentPts).
- `part_pack.lean`: `G7LocalPackU` (no BetaTwist2), `g8LocalPack_of_U`, `g15RamG_of_packU`;
  `tail_glue.lean`: `modularConstituent_tail_U`.
- Compile: LocalGlue.lean exit 0, no sorry, 72 printed declarations all standard axioms;
  TailK.lean exit 0, no sorry, tail_K/R/D/U standard axioms.
- Remaining for LocalGlue on G7's data: leaves R6, I2-Tors (in the bundles); textbook UnramRoots;
  glue KerWild (missing clause of G7Out/TateBridge) and DescentPts (p ≤ 5).

## Step 17 (08:40-08:50 PST): report, KerWild from G7Data's clause
- docs/research/local-glue.md rewritten (main result `localGlue_of_unramRoots`); .fleet/local-glue.md
  written.
- Finding G8 (VERIFIED, read scratch/g0-assemble/parts/75_modfield.lean l.1002-1020): `TateBridge`
  outputs G7Out with ℚ̄_ℓ-valued β' and no relation to G7Data's β or to L' = ker β; KerWild is not
  derivable from its output.
- Proved (VERIFIED, compiled, standard axioms): `kerWild_of_g7Data` — from `G_{L'} = G_L ∩ ker β_ℂ`
  (G7Data's clause; `GQL L = L.fixingSubgroup` in ZInQKernel/HDecomp/Descent/B3Assembly.lean l.36),
  `L'` finite Galois, `β = ι ∘ β_ℂ` with `ι` injective ⟹ `KerWild L' β L` (via copied `resQ_range`).
  So the correction to TateBridge is: also output `β' = ι ∘ β` with `ι` injective.
- Compile: LocalGlue.lean exit 0, no sorry, 73 printed declarations standard.

## Step 18 (08:47-09:05 PST): DescentPts proved for the base change; packs BC
- New part `part_bcdescent.lean` (§7f). Proved (VERIFIED, compiled, standard axioms):
  `qEquiv` (qEmb as ring iso), `jK`, `jL'` (the embeddings L ↪ ℚ̄ inside resQ L, resQ L'),
  `mem_range_jK` (both have image L: `AlgHom.fieldRange_of_normal`), `γL` (= jK_L⁻¹ ∘ jL'),
  `γL_bijective`, algebras `γAlg`, `twAlg`, `compAlg`, `incAlgL` (= g0-mod-field's `incAlg`),
  `tower_tw`, `tower_comp`, `θL` (qEmb_{L'} ∘ qEmb_L⁻¹, L-linear L̄_tw ≃ L̄'), `θL_galois`,
  `conjModel` (A₀ ×_{L,γ} L), `bcL'` ((A₀)_{L'}), `φL` (bcPt ∘ trPt ∘ bcPt⁻¹), `φL_galAct`,
  `dim_conjModel` (pullback along the iso Spec γ is homeomorphic: `Scheme.Hom.homeomorph`,
  `IsHomeomorph.topologicalKrullDim_eq`), **`descentPts_baseChange (A₀) (dim A₀ = 2) :
  DescentPts (K := L') (bcL' hLL' A₀) L`** (L ≤ L' finite, L Galois),
  **`localGlue_of_baseChange`**: LocalGlue for G7Out on (A₀)_{L'} from R6, I2-Tors, UnramRoots,
  dim A₀ = 2, G7Clauses, G_{L'} = G_L ∩ ker β_ℂ, β = ι ∘ β_ℂ with ι injective.
- Finding G9 (VERIFIED, compiled): DescentPts with Mathlib's arbitrary embedding choices inside
  `resQ L`, `resQ L'` needs the conjugate model; it is now built (γ ∈ Aut L).
- `part_pack.lean`: `G7LocalPackBC ℓ r` (g0-mod-field's construction data, no local Prop),
  `g8LocalPack_of_BC`, `g15RamG_of_packBC`; `tail_glue.lean`: `modularConstituent_tail_BC`.
- Compile: LocalGlue.lean exit 0, no sorry, 77 printed declarations standard; TailK.lean exit 0,
  no sorry, tail_{G,L,K,R,D,U,BC} standard.
