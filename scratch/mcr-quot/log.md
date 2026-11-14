# mcr-quot results log

Targets: the glue Props A `FibreAutTame`, B `GenericQuotientP1`, C1 `CMSectionsDisjoint`,
C2 `CoordinateFromSections` of `scratch/mcr-glue/MCRGlue.lean` (copied verbatim as the prefix of
`scratch/mcr-quot/MCRQuot.lean`).

## Step 0 (06:50, 2026-11-14) — VERIFIED
- `scratch/mcr-quot/MCRQuot.lean` = `scratch/mcr-glue/MCRGlue.lean` verbatim. Needs
  `lake build ZInQKernel.Contrib.Mobius.Main ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue`.
- `lake env lean scratch/mcr-quot/MCRQuot.lean`: exit 0, 23 s (compile0_out.txt).
- Tau Ceti / Contrib check: no quotient-by-group, P¹-scheme or fixed-locus piece in
  ZInQKernel/Contrib (directory listing + grep for ToP1/Möbius: only `ImagePlane.inv` (swap charts)
  and the Möbius rigidity of `Contrib/Mobius`). Mathlib 4.35 has the commutative-algebra core of
  quotients: `Algebra.IsInvariant`, `Algebra.IsInvariant.exists_smul_of_under_eq` (transitivity on
  primes), `Ideal.Quotient.stabilizerHom_surjective` (decomposition group onto residue
  automorphisms) in `Mathlib/RingTheory/Invariant/Basic.lean`.
- Computation (py/units.py, VERIFIED): all 72 classes of `(𝒪/3𝒪)^×` (coordinates in the basis
  `1, i, (1+j)/2, (i+k)/2`) contain a unit of `𝒪` (reduced norm ±1) with coordinates in [-3,3].

## Step 1 (07:00) — VERIFIED (MCRQuot.lean = MCRGlue.lean + parts 1-2; exit 0)
- `MCRQuot.exists_unit_congr`: `u₀ ∈ 𝒪` invertible mod `3𝒪` ⇒ some `u ∈ 𝒪^×` with `u ≡ u₀ mod 3𝒪`
  (`𝒪^× ↠ (𝒪/3𝒪)^×`), from `unit_table` (81 cases by `fin_cases`, witnesses from py/units.py,
  checked by `decide`) and the norm form `nrdZ` (`nrdZ_mul`, by `ring`).
- `MCRQuot.TwistEq` (twist-equivalence of objects) with `trans'`, `symm'`, `twistEq_of_iso`.
- `MCRQuot.twistEq_of_mem_fibreAut`: given uniqueness of fibres at `ℚ̄`-points, elements of
  `fibreAut` preserve twist classes (closure induction).
- `MCRQuot.mem_orbit_of_twistEq` (T5 `TorsionStructure` as hypothesis): two `ℚ̄`-points with
  twist-equivalent fibres differ by an element of `fibreAut` (Hecke clauses + `Level3.torsor`
  + `exists_unit_congr` + moduli injectivity).

## Step 2 (07:07) — VERIFIED (parts 1-3; exit 0)
- `MCRQuot.exists_root_smul`, `MCRQuot.exists_comp_smul_eq` (pure algebra): for `A → B` with
  `Algebra.IsInvariant A B G`, `G` finite, two ring maps `φ φ' : B → K` (K a field) agreeing on `A`
  satisfy `φ' = φ ∘ (g • ·)` for some `g ∈ G`. (transitivity on primes + stabilizer onto residue
  automorphisms, both from Mathlib.)
- `MCRQuot.secMap`, `secAction` (the `MulSemiringAction` of `G` on `Γ(X, q⁻¹W)` for an
  `IsGQuotient`), `eq_of_appLE_eq` (a `K`-point is determined by its map on sections of an affine
  open containing it).
- **`MCRQuot.exists_eq_comp_of_isGQuotient`**: for `q : X → Z` with `IsGQuotient G q`, `G` finite,
  two `K`-points of `X` (any field `K`) with `y ≫ q = y' ≫ q` satisfy `y' = y ≫ g` for some `g ∈ G`.

## Step 3 (07:13) — VERIFIED (parts 1-4 + axioms part 9; exit 0; compile4_out.txt; all new
`#print axioms` = [propext, Classical.choice, Quot.sound]; no sorry)
- `MCRQuot.ev_eq_appLE`, `eq_of_ev_eq_chart`, **`val_injective_of_isP1Coordinate`**: an
  isomorphism onto `P¹_{ℤ_(p)}` by charts is injective on field points.
- `MCRQuot.exists_rat_of_fixed`: a Galois-fixed point of `P¹(ℚ̄)` is rational
  (`InfiniteGalois.mem_range_algebraMap_iff_fixed`).
- New glue Prop `MCRQuot.P1ThreePoints` (P¹ geometry over ℤ_(p), no literature): an isomorphism
  `ρ₀ : 𝒵 ≅ P¹_{ℤ_(p)}` and three `ℚ̄`-points with rational `ρ₀`-values and pairwise disjoint
  closures ⇒ some `ρ : 𝒵 ≅ P¹_{ℤ_(p)}` with values `0, ∞, −16/27` there.
- **`MCRQuot.coordinateFromSections_of (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
  (hN : P1ThreePoints) : CoordinateFromSections`** (glue C2 reduced; A is used only for
  `Finite (fibreAut 𝒴 𝒜)`). Finding: C2 as stated needs the finiteness of `fibreAut` (for an
  infinite group `IsGQuotient` does not force orbits = fibres: `ℤ` acting on `𝔸¹_ℚ` by translation
  has `IsGQuotient` onto `Spec ℚ`); A supplies it.

## Step 4 (07:25) — VERIFIED (parts 1-7 + 9; exit 0; compile7_out.txt; standard axioms; no sorry)
- Glue A reduced: **`MCRQuot.fibreAutTame_of (hT : TorsionStructure) (hfix : FibreAutFixFinite)
  (hcnt : TwistClassCard) : FibreAutTame`**. New glue Props: (A-fix) `FibreAutFixFinite`
  (nontrivial elements of `fibreAut` fix finitely many `ℚ̄`-points), (A-count) `TwistClassCard`
  (a twist class has ≤ 288 = 4·72 isomorphism classes). Helper `infinite_qbarPoints` (𝒴 has
  infinitely many `ℚ̄`-points, from `curveFacts.2`). Finding: the bound `p > 324` is exactly what
  makes `|fibreAut| ≤ 288 < p` work.
- Glue C1 reduced: **`MCRQuot.cMSectionsDisjoint_of (hA : FibreAutTame) (hfix : FibreAutFixFinite)
  (hO : GQuotientPointOrbits) (hI : CMStabInvolution) (hS : StabFixesClosure)
  (hC : QbarPointsConjugate) : CMSectionsDisjoint`**. New glue Props (C1a)-(C1d); helpers
  `FixesFieldPointsOn`, `fixOn` (subgroup), `residue_trivial_of_fixesOn` (gives L6's hypothesis),
  `eq_of_involutions_cyclic`.
- Composite **`MCRQuot.modelCoordinateResidue_of_mcrQuot`**: L1-L6 + T5 + glue B + (A-fix),
  (A-count), (C1a)-(C1d), P1ThreePoints ⇒ `ModelCoordinateResidue`.

## Step 5 (07:36) — VERIFIED (parts 1-8b + 9 in build.sh order; exit 0; compile8_out.txt; all
`#print axioms` standard; no sorry in the parts)
- P¹ by charts over ℤ_(p): `MCRQuot.scale` (coordinate `u·ρ`, `u ∈ ℤ_(p)^×`) with
  `isP1Coordinate_scale`, `val_scale`; inversion via the kernel's `ImagePlane.inv` with
  `isP1Coordinate_inv`, `val_inv`.
- `MCRQuot.fromSpec_ker_mem_closure`, **`MCRQuot.isUnit_sub_of_disjoint`**: in a polynomial chart,
  two `ℚ̄`-points with values `a, a' ∈ ℤ_(p)` and disjoint closures have `a − a'` a unit (else the
  point over `(p, h − a)` is in both closures).
- New glue Prop **`MCRQuot.P1Translate`** (translations `t ↦ t + e`, `e ∈ ℤ_(p)`, preserve
  `IsP1Coordinate`), and **`MCRQuot.p1ThreePoints_of : P1Translate → P1ThreePoints`**
  (normalization: `∞`, then `0`, then scale; `zloc_or_inv`, `exists_infty`,
  `integral_of_disjoint_infty`, `exists_unit_neg_16_27`).
- `coordinateFromSections_of' (hA) (hT) (hTr : P1Translate) : CoordinateFromSections`;
  composite `modelCoordinateResidue_of_mcrQuot'` with `P1Translate` in place of `P1ThreePoints`.

## Step 6 (07:41) — VERIFIED (parts 1-6b-8b + 9; exit 0; compile9_out.txt; all 18 MCRQuot
`#print axioms` standard; no sorry)
- Glue B reduced: **`MCRQuot.genericQuotientP1_of (hA : FibreAutTame) (hT : TorsionStructure)
  (hTS : TameQuotientSmooth) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ) :
  GenericQuotientP1`**. New glue Props: (B-desc) `QuotientDescendsQ` (an orbit-invariant map
  `𝒴_ℚ → P¹` descends through the quotient, and `ℚ̄`-points of `𝒵_ℚ` lift), (B-iso)
  `ToP1BijIsCoordinateQ` (a map to `P¹` of a proper smooth ℚ-curve bijective on `ℚ̄`-points is an
  isomorphism by charts). Helper `genFibMap`, `genFibMap_fst`. Leaf L3 is used for `𝒵` proper
  smooth (B's statement does not assume it).
- **Main composite `MCRQuot.modelCoordinateResidue_of_mcrQuot''`**: L1-L6 + T5 + (A-fix),
  (A-count), (B-desc), (B-iso), (C1a)-(C1d), (C2-T) ⇒ `ModelCoordinateResidue`. None of
  mcr-glue's glue A, B, C1, C2 remains a hypothesis.

## Step 7 (08:20) — VERIFIED (parts 1-11 + 9; exit 0; compile11_out.txt; all 25 MCRQuot
`#print axioms` standard; no sorry)
- **(C1a) proved**: `MCRQuot.gQuotientPointOrbits : GQuotientPointOrbits` (primes via
  `IsAffineOpen.primeIdealOf`, `comap_primeIdealOf_appLE`, `exists_smul_of_under_eq`).
- **(C1d) proved**: `MCRQuot.qbarPointsConjugate : QbarPointsConjugate`
  (`exists_algEquiv_comp_eq` via `AlgHom.liftNormal`, `Algebra.IsAlgebraic.algHom_bijective`).
- **(A-count) proved from T5**: `MCRQuot.twistClassCard`. The statement was changed (it is this
  task's own glue, not a target) from `≤ 288` to `≤ 324 = 4 · 81`, which suffices for
  `fibreAutTame_of` because `p > 324`. Helpers `normalizer_T`, `ncard_T_le`, `autOInnerCard`
  (copies of the kernel's `normalizerFinite` / `autOInnerFinite_of_normalizer` proofs with an
  explicit `≤ 4` bound).
- **Final composite `MCRQuot.modelCoordinateResidue_final`**: L1-L6 + T5 + (A-fix), (B-desc),
  (B-iso), (C1b), (C1c), (C2-T) ⇒ `ModelCoordinateResidue`. Also `fibreAutTame_of'` (A from T5 +
  A-fix) and `cMSectionsDisjoint_of'` (C1 from A, A-fix, C1b, C1c).

## Step 8 (08:30) — independent statement review (model, read-only, not compiled)
- A separate model read the Lean text of every new glue Prop (`P1ThreePoints`, `P1Translate`,
  `FibreAutFixFinite`, `TwistClassCard`, `GQuotientPointOrbits`, `CMStabInvolution`,
  `StabFixesClosure`, `QbarPointsConjugate`, `QuotientDescendsQ`, `ToP1BijIsCoordinateQ`,
  helper `FixesFieldPointsOn`) against the definitions. Verdict: all TRUE except
  `QuotientDescendsQ`, true where applied but stated for arbitrary `𝒴` (the descent of a map
  known only by its `ℚ̄`-values needs `𝒴_ℚ` reduced of finite type). Fix applied: added
  `IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →` to `QuotientDescendsQ` (weaker Prop);
  `genericQuotientP1_of` passes `hM.1 hM.2.1`. Recompiled: exit 0.
- Review notes kept for the report: (C1c) needs neither EGA IV 8.13.1 nor smoothness (the closure
  is `Spec R`, `R` a domain with fraction field `κ(x)`); (C1b) stabilizers are cyclic of order
  4, 6, 2 with involutions the images of `i`, `√−3`, `√−6`.

## Step 9 (08:05, resumed run) — VERIFIED (parts through 12 + 9; exit 0; compile12_out.txt; no sorry)
- Part 12: `MCRQuot.translate ρ E : ToP1 X` (for `E ∈ Γ(X, ⊤)`): `U' = U`, `f' = f + E`,
  `V' = D_V(1 + E g) ⊔ D_U(f + E)`, `g'` glued (`objSupIsoProdEqLocus`) from `g/(1+Eg)` and
  `1/(f+E)`; all `ToP1` fields proved (`tS_compat`, `U_inf_tDV_le`, `tF_basicOpen`).

## Step 10 (08:15) — VERIFIED (parts 1-13 + 9; exit 0; compile13_out.txt; standard axioms)
- **(C1c) proved**: `MCRQuot.stabFixesClosure : StabFixesClosure`. Proof: equalizer of `h` and `id`
  in `Over S` is a closed immersion (Mathlib `isClosedImmersion_equalizer_ι_left`, Stacks 01KM,
  needs only `IsSeparated 𝒴.hom`, from `IsProper`); `y` factors through it; closed range contains
  the closure; `exists_factor_of_mem_range_closedImm` (field points over the range of a closed
  immersion factor; `isIso_residueFieldMap_of_closedImm`). Smoothness unused.
- `cMSectionsDisjoint_of'' (hA) (hfix) (hI : CMStabInvolution) : CMSectionsDisjoint`.

## Step 11 (08:45) — VERIFIED (parts 1-14 + 9; exit 0; compile14_out.txt; all `#print axioms`
standard; no sorry in the parts)
- **(C2-T) proved**: `MCRQuot.p1Translate : P1Translate`. Pieces (part 14): `tH = 1 − e g'`,
  `basicOpen_tg` (`D(g') = D_U(f+e)`), `basicOpen_tH` (`D(1 − e g') = D_V(1+eg)`),
  `isAffineOpen_V'` (Mathlib `isAffineOpen_of_isAffineOpen_basicOpen`, Stacks 01QF, with the
  spanning pair `g', 1 − e g'`), `exists_poly_DU` / `exists_poly_DV` (sections on the two basic
  opens are polynomials in `g'` up to powers; `eval₂_reflect_mul_pow`, `eval₂_eq_sum_range'`),
  `exists_pow_mul_eq_of_res` (`isLocalization_of_eq_basicOpen`), `surjective_g'` (coprimality of
  `Y^a`, `(1 − eY)^b`), `injective_g'` (`Γ(U)` a domain, localization injective, `reflect`),
  `bijective_eval₂_add`, `isP1Coordinate_translate`, `val_translate`.
- `coordinateFromSections_of'' (hA : FibreAutTame) (hT : TorsionStructure) : CoordinateFromSections`.
- **Final composite `modelCoordinateResidue_final2`**: L1-L6 + T5 + (A-fix), (B-desc), (B-iso),
  (C1b) ⇒ `ModelCoordinateResidue`.

## Step 12 (09:30) — VERIFIED (parts 1-15 + 9; exit 0; compile15_out.txt; standard axioms)
- **(A-fix) reduced**: `MCRQuot.fibreAutFixFinite_of (hC : CurveBijIso) (hYI : ModelYIrreducible)
  (hF : CurveClosedQbarFinite) : FibreAutFixFinite`. `CurveBijIso` is model-glue's textbook leaf
  (in the prefix). New: input `ModelYIrreducible` (Y irreducible over ℚ), glue
  `CurveClosedQbarFinite` (closed subset of an integral smooth relative curve over ℤ_(p) missing the
  generic point carries finitely many ℚ̄-points). Helpers `isIntegral_model` (model-glue's
  `modelIntegral_of` argument with `ModelYIrreducible` for the chart), `eq_one_of_genericPoint_fixed`
  (closed equalizer + `isIso_of_isClosedImmersion_of_surjective`).
- Finding: A-fix, hence the reductions of A and C1, need the ℚ-irreducibility of `Y` (equivalently
  of `𝒴`); the targets A, C1 do not carry the normalization chart `E` from which model-glue derives
  it (`irreducible_of_chart`). Mathematically true for `Y₃` (π₀ ≅ (ℤ/3)^×, Galois-conjugate
  components; SPECULATIVE reading, locator UNVERIFIED).
- `fibreAutTame_of''`, `modelCoordinateResidue_final3` (L1-L6, T5, CurveBijIso, ModelYIrreducible,
  CurveClosedQbarFinite, B-desc, B-iso, C1b).

## Step 13 (10:10) — VERIFIED (parts 1-16 + 9; exit 0; compile16_out.txt; standard axioms)
- `CurveClosedQbarFinite` amended (own glue): added `IsProper 𝒴.hom` (without quasi-compactness it
  is false: 𝔸¹ with infinitely many doubled points). `fibreAutFixFinite_of` passes `hM.1`.
- **(A-fix-dim) proved**: `MCRQuot.curveClosedQbarFinite : CurveClosedQbarFinite`. Pieces:
  `finite_residueField_of_isClosed` (Zariski via `isClosed_singleton_iff_isClosedImmersion` +
  `HasRingHomProperty.Spec_iff` + `finite_of_finite_type_of_isJacobsonRing`),
  `finite_qbarPts_over_closed`, `finite_of_isClosed_of_closedPoints` (Noetherian + quasi-sober),
  closedness of points of `Z ∩ 𝒴_ℚ` from `smoothStalkDimOne` + `ringKrullDim_stalk_eq_coheight`
  + `Order.coheight_add_one_le`.
- `fibreAutFixFinite_of' (hC : CurveBijIso) (hYI : ModelYIrreducible) : FibreAutFixFinite`.
- **Final composite `modelCoordinateResidue_final4`**: L1-L6 + T5 + CurveBijIso +
  ModelYIrreducible + (B-desc) + (B-iso) + (C1b) ⇒ `ModelCoordinateResidue`.
