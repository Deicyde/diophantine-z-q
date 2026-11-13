# prop-ts results log

Base f90cf864 (wip/prop-ts). Object: `G0ModField.PropTS`, `PropTSAll` from
`scratch/fibre-cover/FibreCover.lean`, copied into `scratch/prop-ts/PropTS.lean`;
`check_identical.py`: both IDENTICAL (VERIFIED).

## Step 1 (06:40): leaf + glue + reduction, compiled
- Build: `lake build ZInQKernel.HDecomp.QM.Leaves ZInQKernel.HDecomp.Descent.B2Glue
  ZInQKernel.HDecomp.QM.Pin` OK.
- `lake env lean scratch/prop-ts/PropTS.lean`: 0 errors (VERIFIED, compile_out.txt).
- Defs: `InfCoord` (ℚ[s], s ↦ X⁻¹), `infAlg`, `intPolyAlg`, `vertPrime`, `BranchData`,
  `NoVerticalRam`, `BeckmannSIT` (leaf), `FunctionFieldModel`, `nY3`, `CoverBranchData`,
  `CoverModel`.
- Theorems (axioms [propext, Classical.choice, Quot.sound], VERIFIED):
  `padicValRat_16_27`, `propTS_of_coverModel : BeckmannSIT → CoverModel Y π → PropTS Y π`,
  `propTSAll_of_coverModel`.

## Step 2 (06:45): pin route + leaf (a) weakened to `[E : ℚ(X)] < p`
- `BeckmannSIT` hypothesis (a) is now `Module.finrank (RatFunc ℚ) E < p` (weaker than `p ∤ |G|`,
  so the leaf is implied by any version of Beckmann's theorem).
- New, compiled, standard axioms (VERIFIED): `residueImage_comp_eq_of_pt` (Φ' = Φ ∘ g ⇒
  ℚ(g∘y') = ℚ(y')), `propTS_transfer` (along kernel `Pin.SameTripleMor`),
  `propTSAll_of_witness` (kernel `MobiusGlue` + `R1R2fp` + PropTS on one triple),
  `propTSAll_of_leaves : BeckmannSIT → R1R2fp → MobiusGlue → CoverModelOfHecke → PropTSAll`.
- Copied with proofs from fibre-cover: `spec_to_specQ_eq`, `exists_factor_of_residueImage_le`,
  `residueImage_le_aux`, `residueImage_comp_le_self_aux`.
- Sanity: `example (h : BeckmannSIT) := h (RatFunc ℚ)` elaborates (instances satisfiable).

## Step 3 (06:50): Beckmann as glue from purity + T2 (Abhyankar), compiled
- New defs: `NonMeeting`, `SpecNonMeeting` (glue from purity, t-purity3), `KummerStep`,
  `KummerGlue := PkgI2.AbhyankarDVR.{0} → KummerStep`, `UnramifiedMono` (textbook),
  `BeckmannSITTame` (BeckmannSIT + `0 < n_b < p`, `0 < nInf < p`).
- New theorems, standard axioms (VERIFIED): `beckmannSITTame_of`, `beckmannSITTame_of_glue :
  KummerStep → SpecNonMeeting → UnramifiedMono → BeckmannSITTame`, `propTS_of_coverModel_tame`,
  `propTSAll_of_bundle : AbhyankarDVR → R1R2fp → KummerGlue → SpecNonMeeting → UnramifiedMono →
  MobiusGlue → CoverModelOfHecke → PropTSAll`.
- `NonMeeting` requires `f.eval s₀ ≠ 0` explicitly (padicValRat p 0 = 0 would otherwise let a
  vanishing f count as a unit).

## Step 4 (07:00): UnramifiedMono proved
- `unramifiedMono : UnramifiedMono` compiled, standard axioms (VERIFIED). Uses Mathlib's
  `Ideal.exists_ideal_over_prime_of_isIntegral`, `Ideal.ramificationIdx_below_dvd`, and the
  instances `Algebra (𝓞 L) (𝓞 L')`, `Module.Flat` (Dedekind + torsion-free).
- `propTSAll_of_bundle' : AbhyankarDVR → R1R2fp → KummerGlue → SpecNonMeeting → MobiusGlue →
  CoverModelOfHecke → PropTSAll` (VERIFIED).
- Note: this also proves fibre-cover's tower direction "subfield of unramified is unramified"
  (fibre-cover's `UnramifiedConjugates` is the other direction, compositum; not done).

## Step 5 (07:15): non-meeting case of KummerStep proved
- `SpecNonMeeting` conclusion now `FiniteDimensional ℚ L ∧ UnramifiedAt L p` (finiteness of the
  residue field moved from KummerStep into the purity glue, where it belongs).
- New: `KummerMeet` (KummerStep restricted to `v_p(t) < 0 ∨ ∃ b ∈ S, v_p(t − b) > 0`),
  `KummerMeetGlue := AbhyankarDVR → KummerMeet`; theorems `padicValRat_sub_nonneg`,
  `kummerStep_of_meet : KummerMeet → KummerStep`, `propTSAll_of_bundle_meet`.
- Compile: 0 errors, 0 warnings; 16 `#print axioms`, all [propext, Classical.choice, Quot.sound]
  (VERIFIED).

## Step 6 (07:10): FunctionFieldModel from a normalization statement, compiled
- New: `exists_factor_scheme`, `residueImage_specMap` (ℚ(Spec ψ) = ℚ(ψ(B))),
  `residueImage_comp_openImmersion`, `NormalizationModel` (glue: open immersion
  `Spec B → Y` onto the `ℚ̄`-points with finite `π`, with `π = X` along it),
  `functionFieldModel_of_normalization`, `CoverModelN`, `coverModel_of_N`, `CoverModelOfHeckeN`,
  `propTSAll_of_bundle_N`.
- Compile: 0 errors, 0 warnings, 22 `#print axioms` lines all standard (VERIFIED).

## Review (independent model agent, read-only, 07:10)
- No false, vacuous or junk-value-exploitable statement found.
- Docstring fixes requested: (1) BeckmannSIT for non-regular E: derive from the regular case over
  the constant field k' (NoVerticalRam forces k' unramified at p); (2) NoVerticalRam docstring:
  separability from `[E:ℚ(X)] < p`, not `p ∤ n`; (3) BeckmannSIT (a) wording ("stronger
  hypothesis, weaker leaf"); (4) FunctionFieldModel truth needs π Γ'-invariant and non-constant on
  components. Applied in step 7.

## Step 7: review docstring fixes applied; recompiled 0 errors, 22 standard-axiom lines; copies still IDENTICAL (VERIFIED).

## Step 8 (07:20): PropTS refuted for an arbitrary cover (sanity), compiled
- `not_propTS_cyclotomic : ∃ Y₀ π₀, ¬ PropTS Y₀ π₀` with `Y₀ = fieldPt ℚ(ζ₃₃₁)`, `π₀ = constOne`
  (charts ⊤, f = g = 1), `t = 1`, `p = 331`: uses `residueImage_specMap`, `constOne_val`,
  `padicValRat_43_27`, Mathlib `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime` (e = 330).
  So PropTS is a genuine constraint on the cover, not inert or tautological (VERIFIED).
- Compile: 0 errors, 0 warnings, 24 `#print axioms` lines all standard (VERIFIED).

## Step 9 (07:30): building block for SpecNonMeeting
- `scratch/prop-ts/ZXRegular.lean` (imports Mathlib only): `height_maximal_intPoly` (a maximal
  ideal of ℤ[X] over a nonzero prime of ℤ has height 2, via Mathlib
  `Polynomial.height_eq_height_add_one`) and `regular_dim2_intPoly` (`ℤ[X]_m` is regular local of
  dimension 2; regularity from Mathlib's instances `IsRegularRing ℤ[X]` (Dedekind ⇒ regular,
  polynomial over regular)). Compiled, standard axioms (VERIFIED, compile_zx.txt).
- Note: Mathlib v4.35 has no `IsJacobsonRing ℤ` instance; the lemma takes `m ∩ ℤ ≠ 0` instead.
