# g0-fibresimple results log

## Setup
- 01:45 merged origin/wip/g0-split (base for Split.lean). FibreSimple's statement is identical in
  origin/wip/leaf-adopt3's Leaves.lean (VERIFIED by grep).
- Infrastructure: `olean/FSPrefix.lean` = verbatim copy of scratch/g0-split/Split.lean (gitignored; regenerate
  with build_prefix.sh), compiled to an olean; `olean/Tail.lean` imports it (`ctail.sh`).
- `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` was needed first (OK).
- 01:53 prefix olean built (231 s, exit 0).

## Decomposition (Tail.lean)
- 01:58 `G0FibreSimple.fibreSimple_of_pieces : QMDichotomyYu → EndDivisionDescent → EndDivisionOfSchemeIso →
  EndDivisionOfEnd0Division → CentralizerOfMatrixEnd0 → FibreComTrivial → HSyn.G0Split.FibreSimple` COMPILED
  (exit 0, 38 s against the prefix olean); `#print axioms`: propext, Classical.choice, Quot.sound.
  Also `fibreSimple_of_leaves (t : TextbookLeaves) (p : FibreSimplePieces)` (T27 is `TextbookLeaves.t27`).
- Proved glue (VERIFIED, compiled): `B6_isUnit` (B = (2,-3) division, from GlueDescent.aniso_rat),
  `qm_embeds_end0` (QMStr gives ℍ[ℚ,2,-3] →ₐ[ℚ] End0 A via QuaternionAlgebra.Basis.liftHom, i ↦ 1⊗ι(i), j ↦ 1⊗ι(j)
  with j = 2·(1+j)/2 − 1 ∈ 𝒪).

## Finding: R1fpProps/R2fpProps do not pin down Φ on closed points
- 02:00 COMPILED (exit 0, 101 s): `PtAuto Y` (natural automorphism σ of the field-point functor), `twistBy Φ σ`,
  `r1fpProps_twistBy` (R1fpProps invariant, no condition), `r2fpProps_twistBy` (R2fpProps invariant if σ permutes the
  π-fibres of ℚ̄-points and fixes the fibres over 0, ∞, −16/27), `fibreComTrivial_twisted`. Standard axioms.
- Consequence (argument, SPECULATIVE in its arithmetic part): with the true data (Y₃, Φ, π), a natural σ exchanging
  the π-fibre over t₁ = J(u) with the fibre over a rational non-branch CM value t₂ exists iff the two fibres are
  isomorphic Gal(ℚ̄/ℚ)-sets (closed points with ℚ-isomorphic residue fields). For such σ, FibreSimple at
  (Y₃, Φ∘σ, π) asks a CM surface to be simple: false. So FibreSimple ⇔ NoCM ∧ "no such coincidence"; the second
  conjunct is not a published theorem and is not decided here.

## FS4 proved
- 02:04 COMPILED (exit 0, 23 s): `centralizerOfMatrixEnd0_of_homFree : PkgI3.HomFreeFinite → CentralizerOfMatrixEnd0`
  (scalar matrix √d central; ℚ ⊗ End A = localization (isLocalizedModule_iff_isBaseChange); freeness from T6 gives
  injectivity of m ↦ 1⊗m). `fibreSimple_of_pieces'` and `fibreSimple_of_leaves (t : TextbookLeaves)
  (p : FibreSimplePieces)` now use T6 = `TextbookLeaves.t6`, T27 = `TextbookLeaves.t27` and four glue pieces
  FS1 EndDivisionDescent, FS2 EndDivisionOfSchemeIso, FS3 EndDivisionOfEnd0Division, FS5 FibreComTrivial.
  All standard axioms.

## FS3 proved
- 02:07 COMPILED (exit 0, 69 s; rerun 19 s after bundle edit): `end0Division_of_homFree : HomFreeFinite → MulIsogeny →
  EndDivisionOfEnd0Division`. New textbook leaf `MulIsogeny` (Mumford §4 Application 2, locator UNVERIFIED: `[n]`,
  `n ≠ 0`, finite and surjective, char 0). Proof: clear denominators of u⁻¹ (localization), g∘f = f∘g = [s];
  Mathlib `IsFinite.of_comp` (g separated: `IsSeparated.of_comp` with `Over.w`) and `Surjective.of_comp`.
- `fibreSimple_of_leaves (t : TextbookLeaves) (hMul : MulIsogeny) (p : FibreSimplePieces)`, bundle = FS1
  EndDivisionDescent, FS2 EndDivisionOfSchemeIso, FS5 FibreComTrivial. Standard axioms.

## Standalone
- 02:11 `lake env lean scratch/g0-fibresimple/FibreSimple.lean` (20474 lines = Split.lean + Tail): exit 0 in 174 s,
  0 errors, no `sorry` warning; `#print axioms` standard three for HSyn.glueOutputs_of_leaves and all 11 new
  theorems (full_out.txt).

## FS2 proved
- 02:13 COMPILED (exit 0, 18 s): `endDivisionOfSchemeIso_of_rigidity : RigidityHom → EndDivisionOfSchemeIso`.
  New textbook leaf `RigidityHom` (Mumford §4 Cor. 1 / Milne Cor. 2.2, locators UNVERIFIED: a k-morphism of abelian
  varieties with η ≫ h = η is IsMonHom). Proof: ψ = e − e(0), ψ' = e⁻¹ ∘ (· + e(0)) in the group of morphisms into
  the group object; inverse to each other, preserve η, hence homomorphisms; conjugation.
- `fibreSimple_of_leaves (t : TextbookLeaves) (hMul : MulIsogeny) (hRig : RigidityHom) (p : FibreSimplePieces)`,
  bundle = FS1 EndDivisionDescent, FS5 FibreComTrivial.

## FS1 reduced
- 02:18 COMPILED (exit 0, 22 s): `endDivisionDescent_of : BaseChangeFaithful → IsogenyDescends → EndDivisionDescent`
  (FS1a: Over.pullback along Spec L → Spec K faithful; FS1b: IsIsogenyMor descends along it; both pure scheme
  theory, STANDARD fpqc descent). Uses `Functor.map.instIsMonHom` (explicit instance: A_L's grp vs monObjObj)
  and `Functor.map_one`.
- Bundle `FibreSimplePieces` = FS1a, FS1b, FS5.

## FS1a proved, FS1b reduced to finiteness descent
- 02:24 COMPILED (exit 0, 21 s; 19 s after bundle edit): `specMap_flat_surjective` (Spec L → Spec K flat and surjective,
  via `flat_and_surjective_SpecMap_iff` + `RingHom.faithfullyFlat_algebraMap_iff`), `baseChangeFaithful_proof :
  BaseChangeFaithful` (Mathlib instance `(Over.pullback f).Faithful` for surjective flat quasi-compact f, in
  Morphisms/FlatDescent.lean), `isogenyDescends_of : FiniteDescends → IsogenyDescends` (surjectivity via the base
  change square, `Surjective.of_comp`).
- Remaining glue in the bundle: FS1b′ `FiniteDescends` (IsFinite descends along a field extension; Mathlib has
  `RingHom.Finite.codescendsAlong_faithfullyFlat` and `HasAffineProperty.descendsAlong_of_affineAnd` but no
  `IsAffineHom` descent instance) and FS5 `FibreComTrivial`.
- 15 `#print axioms` lines, all [propext, Classical.choice, Quot.sound].
