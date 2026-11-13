# g0-mod-field results log

## Setup
- Base 883c4ddf + merge of origin/wip/g0-split (for scratch/g0-split/Split.lean, ModularConstituent).
- Built once: `lake build ZInQKernel.HDecomp.QM.Leaves` (2 min), `lake build ZInQKernel.Hypotheses.JHeight`
  (builds upstream lean/ helpers; needed for any import that reaches `ZInQ.*`).
- `ZInQKernel.Main` cannot be imported from scratch in this tree; `le_heightD_of_mem_S_mul` copied.

## run1-5 (02:00): scratch/g0-mod-field/ModField.lean
- Statements: `FibreCtx`, `IsModelOver`, `G2Out`, `DescentDatum`, `G4Out`, `G7Out`, `FibreCoverOut`,
  `KernelFieldOut`, `FibreCoverExists`, `KernelFieldExists`.
- Proved: `baseChangeTrans`, `isModelOver_baseChange`, `admissible_S_mul`, `g7Out_of_g4Out`,
  `g2Out_of_cover`, `g4Out_of_kernelField`, `fieldDescent`.
- VERIFIED: `lake env lean scratch/g0-mod-field/ModField.lean`: 0 errors, no sorry;
  `#print axioms fieldDescent`, `g7Out_of_g4Out`: [propext, Classical.choice, Quot.sound].

## run6-9 (02:05): twist and unramifiedness of L'
- Built `ZInQKernel.HDecomp.B3Unram.T32a` (oleans absent before).
- New: `b3_of_cochain` (glue-descent's B3 proof with B2's cochain as hypotheses), `two_mem_T`,
  `G7Data` (clause list), `G7OutUnr`, `g7OutUnr_of_g4Out` (B2 + `GlueB3Unram.unramified_outside_noLeaf`
  + B3 + `degree_le_QM`), `g7Out_of_g7OutUnr`.
- Pitfall: `open MonObj` makes `η` a token; binder names `η` fail to parse.
- VERIFIED: 0 errors; `#print axioms g7OutUnr_of_g4Out`: [propext, Classical.choice, Quot.sound].

## run10 (02:06): feed to ModularConstituent
- Built `ZInQKernel.HDecomp.I3Linalg.C2`, `ZInQKernel.HDecomp.ModCurves.Defs`.
- New: `fieldDescentUnr`, `CommonConstituent` (copied verbatim from part_split.lean),
  `ModularConstituentG` (part_split's `ModularConstituent` over `PkgI3.AbVar`), `AfterG7` (G8-G16 as
  one Prop over `G7Data`), `modularConstituent_of_ranges` (FibreCoverExists, KernelFieldExists, four
  B2 leaves, AfterG7 ⊢ ModularConstituentG).
- VERIFIED: 0 errors; axioms of `modularConstituent_of_ranges`, `fieldDescentUnr`:
  [propext, Classical.choice, Quot.sound]. The emb.toAlgebra clause closed by the G7Data clause
  directly (defeq of `(algebraMap L' ℚ̄).toAlgebra` with the intermediate-field instance).

## run11-14 (02:11): B1 normalization proved; KernelFieldOut refined
- `KernelFieldOut u P K A` now asks only for `E` (Galois image `G ≤ GL_r(ℤ)`, `r ≤ 16F₀²`,
  `[E:ℚ] = |G|`, `E` unramified outside `T`) and `ConjugacyData` on the base change `A_{E⊔K}`;
  the model over `E ⊔ K` is proved (`isModelOver_baseChange`), the unramifiedness of `E ⊔ K` is the
  named standard Prop `UnramifiedSup`.
- New: `sgnU`, `sgnU_sq`, `sgnU_mul`, `sgnU_mul_abs`, `ConjugacyData`, `normA`,
  `descentDatum_of_conjugacy` (B1, N5 L645-663: `a_σ = |ker m_σ|^{-1/4}`, `ε = sgn c`; local constancy
  via `isLocallyConstant_of_openSubgroup` on `G_L × G_L`).
- VERIFIED: 0 errors; all six `#print axioms` lines: [propext, Classical.choice, Quot.sound].

## run15 (02:12): `a` pinned on G_L
- Found (model check): `DescentDatum` without constraints on `a` over `G_L` leaves `a` free up to a
  character `G_ℚ → ℝ_{>0}`; g0-mod-galois' `G7Out` asks `a = 1` on `G_{L'}`. Added to `DescentDatum`:
  `a k = 1`, `a (σk) = a σ`, `a (kσ) = a σ` for `k ∈ G_L`; to `ConjugacyData`: the matching kernel-size
  clauses (`|ker m_k| = 1`, `|ker m_{σk}| = |ker m_{kσ}| = |ker m_σ|`). `descentDatum_of_conjugacy`
  re-proved.
- VERIFIED: 0 errors, all axioms standard.

## run16-17 (02:14): T14-T15 form
- Built `ZInQKernel.HDecomp.Descent.WP3`. New: `modularConstituent_of_ranges_T14` (LeafHasse,
  LeafLocalTwo replaced by the bundle's `PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`,
  `LocalH2CardC` via `GlueWP3.leafHasse_of_T14`, `leafLocalTwo_of_T15`).
- VERIFIED: 0 errors; axioms standard. File: 640 lines, `lake env lean` ~10 s after imports cached.

## run18-21 (02:18): bridge to g0-mod-galois' inputs
- Copied from wip/g0-mod-galois (20fa1287) `resQ`, `Vb`, `tate`, `G2Out`, `G7Out` (namespace
  `G0ModField.GaloisCopy`).
- New Props: `ResQRange` (image of `resQ L'` is `Fix(L')` for finite Galois `L'`), `TateBridge`
  (G7Data + dim 2 + rank End 4 ⊢ ∀ ℓ, ∃ data, GaloisCopy.G7Out on `A_{L'}`).
- Proved: `galoisG2Out_of_g7Data` (their G2Out for `K = L'` from G7Data's B3(v) clause and
  `ResQRange`; `PkgI4.LiesOver` and `GlueB3Unram.LiesOver` agree by defeq).
- VERIFIED: 0 errors; axioms standard.

## run22 (02:21): ResQRange attempt (abandoned)
- Tried a Mathlib-only proof of `ResQRange` (`absoluteGaloisGroup.map` unfolds to
  `restrictNormalHom ∘ restrictScalarsHom` with local instances `(algebraMap ℚ K).toAlgebra` and
  `IsAlgClosed.lift`); first compile hit instance mismatches between the intermediate-field
  `Algebra ℚ L'` and `map`'s local one. Proof outline (true): `g : ℚ̄ → \bar L'` maps `L'` onto the
  image of `L'` (normality, `AlgHom.fieldRange_of_normal`), so `resQ σ` fixes `L'`; conversely lift
  `τ ∈ Fix(L')` by `AlgEquiv.restrictNormalHom_surjective`. Left as the named Prop; file removed.

## run23-26 (02:25): three truth repairs of the interface (model checks)
1. `KernelFieldExists` quantified over every `K`-model `A` of `P`: FALSE in general (a twist of the
   fibre by a cocycle ramified at `p ∉ T` has bad reduction at `p`, so `E` may ramify outside `T`).
   Fix: new `RationalFibre Y Φ P K PK` (a `K`-point `yK` of `Y₃` with object `PK : QML3 K` whose base
   change carries `P`, and `PK.A` a model); `G2Out`, `FibreCoverOut` produce it; `KernelFieldExists`
   quantifies over it.
2. `AfterG7` quantifies over every `G7Data`; with `A` an arbitrary model the same twist problem breaks
   G11/G15. Fix: new `IsQMModel L A P` (`A` is the base change of `PK.A` for a `QML3` object `PK`
   over `K ≤ L`; good reduction away from 3 by G3) replaces `IsModelOver L A P` in `G4Out`, `G7Out`,
   `G7Data`; `IsQMModel.isModelOver` proved.
3. `G7Data` allowed any `χ` with modulus supported on `T`; `χ λ²` with `λ` wild at a large `p ∈ T`
   would break G15's exponent bound `≤ 2`. Fix: clause `∃ T₋ ⊆ T, N = chiLevel T₋`
   (`= ∏ lev p`, `lev 2 = 4`); `b2_of_leaves_level` (copy of `b2_of_leaves` exposing the level) proves it.
- VERIFIED: 0 errors; all eight `#print axioms`: [propext, Classical.choice, Quot.sound].

## run27-28 (02:28): kernel clauses derived
- New: `galAct_bijective` (from `galHom_mul`, `galHom_one`), `toLAut` (`k ∈ G_L` as an
  `L`-automorphism, `AlgEquiv.ofRingEquiv`), `card_ker_GL` (`|ker m_k| = 1`, `|ker m_{σk}| = |ker m_{kσ}| =
  |ker m_σ|` from the first two clauses of `ConjugacyData`). The corresponding clause removed from
  `ConjugacyData`.
- VERIFIED: 0 errors; axioms standard.
