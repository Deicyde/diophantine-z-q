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
