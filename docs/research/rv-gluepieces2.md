# rv-gluepieces2: adversarial truth review of the 27 fields of `GluePieces2`

Task rv-gluepieces2, 2026-11-13.
- **Object:** `structure HSyn.GluePieces2` in `scratch/g0-assemble/G0Assemble.lean` (L41938-41998;
  docs/research/g0-assemble.md §2). G0Assemble.lean was not edited.
- **Scratch:** `scratch/rv-gluepieces2/`. It holds the results log `log.md`; the Lean checks
  `checks/c1…c9`, compiled over an olean of the post-pin-apply `Leaves.lean` (`olean/*_out.txt` are
  the compiler outputs); the four per-area review notes `review-{misc,height,galois,newform}.md`; and
  the scripts `build_prefix.sh`, `assemble.sh`, `ctail.sh`, `gen_at.py`.

Marks: **VERIFIED** = compiled with Lean here, or read and diffed in a file. **STANDARD** = published,
with a reference. **SPECULATIVE** = a model argument. **UNVERIFIED** = theorem number from memory (no
network). This is model work only; there has been no human review.

## 0. Verdict

**No field is refuted. Twenty-one fields are TRUE. Six are UNSURE as stated in G0Assemble.lean,
because they cannot be proved over the file's copy of the QM leaf. The repair already exists in the
repository, and it is checked here in Lean.**

1. **The rv-g0pieces defect is still present in G0Assemble.lean.** VERIFIED by diff:
   `scratch/g0-assemble/Leaves.lean`, from which G0Assemble.lean is generated, is the copy of
   `scratch/h-decomposition/Leaves.lean` taken before pin-apply. In it, `R1fpProps` (L15152) has
   only the four clauses (proper, smooth, a ℚ̄-point, naturality). It lacks `R1famProps` and
   `R1univProps`.
   - Six fields quantify over every triple `(Y, Φ, π)` with `R1fpProps ∧ R2fpProps`, either directly
     or through `FibreCtx`:
     - 4 `fibreComTrivial`;
     - 10 `fibreQMPeriod`;
     - 12 `fibreCoverExists`;
     - 13 `kernelFieldExists`;
     - 27 `modelG3G6`, its G6 half;
     - 28 `linkedTateData`.
   - Under the four-clause list, a natural relabeling of points can attach the fibre over another
     rational value of π to `J(u)`. The file itself proves this (`G0FibreSimple.r1fpProps_twistBy`,
     `fibreComTrivial_twisted`, parts/40_fibresimple §5).
   - So each of the six fields as stated is equivalent to an open arithmetic statement: no rational
     fibre outside the contact set is ℚ-isomorphic, as a finite étale scheme, to a CM fibre or to a
     fibre with the wrong height or ramification. Nobody can prove that today.
   - g0-assemble.md marks only fields 4, 10, 13 and 27 as QM-PIN. **Fields 12 and 28 are in the same
     class** (new finding), because both quantify through `FibreCtx`. fibre-cover's reduction of
     12 had to use the pin-free Prop `PropTSAll`, which is SPECULATIVE.
2. **Repair, checked in Lean.** Rebuild G0Assemble.lean on the current
   `scratch/h-decomposition/Leaves.lean`.
   - **The composite compiles unchanged** (VERIFIED). `gluePieces_of_gluePieces2` and
     `sixContactMin_of_leaves2` compile with standard axioms. Only the two §5 demonstration lemmas
     of parts/40_fibresimple, which are used nowhere downstream, needed an extra hypothesis.
   - **Each of the six fields then follows from its statement for one triple** (VERIFIED,
     `checks/c9_pin_transfer.lean`), given pin-apply's named glue `Pin.MobiusGlue` and the bundle's
     `R1R2fp`. The proved theorems are `fibreComTrivial_of_at`, `fibreQMPeriod_of_at`,
     `fibreCoverExists_of_at`, `kernelFieldExists_of_at`, `modelG3G6_of_at` and
     `linkedTateData_of_at`.
   - For the genuine triple all six are true: Glazer §4 with the NoCM step A10 (SPECULATIVE, as in
     rv-g0pieces).
3. **Two fields are true but not provable from their hypotheses:**
   - **17 `g9Glue`** needs `R10Weights` (Tate–Sen content; the bundle's `r10` was never amended as
     g9-derham asked) and `AbVarBaseChange`.
   - **18 `g10Glue`** needs the Artin comparison T12, which needs T35, T5 and T26. Those are bundle
     leaves, but they are not hypotheses of `G10Glue`, and `g8_g11` does not pass them.

   As stated, these two hide literature content inside "glue". The repair is to add the hypotheses
   (§3).
4. **Two "glue" fields need the analytic uniformization theorem**, which is a leaf:
   5 `analyticUniformizationUnique` and 7 `metrizationExists`. Both are TRUE, but they are
   classified wrongly.
5. **Lean status on G0Assemble's own constants** (VERIFIED, standard axioms, no `sorry`).
   - **Proved outright:** 3, 6, 14, 15 (`BurnsideAbsIrred`, claimed as a leaf, proved here from Mathlib), 24, 25, 26. Field 22 follows from the bundle leaf `t17`.
   - **Reduced:** 7, 8, 9, 12, 17, 19 and 20 to the named Props of the wave-27 tasks. Field 18 is
     reduced to `ConjTwistNontrivial`: g10-odd's reduction applies to g0-assemble's changed
     statement.
   - These checks settle the transfer caveats raised in this review. Field 9 (height-bc) needed one
     `open` line removed, so that `AbVar` is G0Assemble's `DefFaltings` copy. Field 22 needed
     `hiding Qbar GQ`. Field 12 needed the six-clause `obtain`.

6. **`GluePieces3`: 15 fields in place of 27, compiled** (VERIFIED, `final/c12_bundle.lean`, over
   the pinned prefix with checks c1-c11 imported):

   ```lean
   theorem HSyn.sixContactMin_of_leaves3 (r : ResearchLeaves) (t : TextbookLeaves)
       (gp : GluePieces3) : ZInQ.SixContactMin
   ```

   - **Kept as fields (13):** `mulIsogeny`, `rigidityHom`, `analyticUniformizationUnique`,
     `metrizationExists`, `productMetrizationGeo`, `hodgeLineBaseChange`, `thetaRatiosAlgebraic`,
     `r14Det`, `g9Glue`, `conjTwistNontrivial` (in place of `g10Glue`), `g12Weight`, `detTate`,
     `carayolR17`.
   - **Added (2):**
     - `mobius : Pin.MobiusGlue`;
     - `qmAt : ∃ Y Φ π, R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧` the six one-triple forms.
   - Everything else is proved: `gluePieces2_of_3` builds all 27 fields of `GluePieces2`.

## 1. Per-field verdicts, worst first

Columns: verdict, the attack tried, evidence, Lean status here. "Lean" means a check compiled on
G0Assemble's own constant, over the pinned prefix (§2).

| # | field | verdict | main attack and finding | Lean here |
|---|---|---|---|---|
| 4 | `fibreComTrivial` | **UNSURE as stated** (pin); TRUE after repair for the genuine triple | relabeling (proved in-file, §5 of part 40): asserts NoCM at every rational value whose π-fibre can be exchanged with the one over `J(u)` | `fibreComTrivial_of_at` (pinned) |
| 10 | `fibreQMPeriod` | **UNSURE as stated** (pin); TRUE after repair | a relabeled `A` lies over `c ≠ J(u)`, so `j_θ(Ω(τ)) = J(u)` fails if a coincidence exists | `fibreQMPeriod_of_at` |
| 12 | `fibreCoverExists` | **UNSURE as stated** (pin; not flagged QM-PIN by g0-assemble); TRUE after repair | through `FibreCtx`; fibre-cover's pin-free route needs `PropTSAll` (SPECULATIVE Hilbert-irreducibility argument) | reduced: `RvGP2.fibreCoverExists` (T5, `InnerTwistCount`, `PropTSAll`, `UnramifiedConjugates`); `fibreCoverExists_of_at` |
| 13 | `kernelFieldExists` | **UNSURE as stated** (pin); TRUE after repair | `ConjugacyData` asks `m_σ` to commute with all of `End_{E⊔K}(A)`; for a CM fibre this plausibly fails when `σ` moves the CM field (SPECULATIVE). The `r ≤ 16F₀²` and `[E:ℚ] = |G|` clauses are loose but true | `kernelFieldExists_of_at` |
| 27 | `modelG3G6` | G3 half **TRUE**. G6 half **UNSURE as stated** (pin), TRUE after repair | G3: `Level3` = full rational 3-torsion, so Raynaud's criterion (SGA 7 IX 4.7, UNVERIFIED) plus potential good reduction (QM) give good reduction at `p ≠ 3` (STANDARD). `G3Out` excludes `p = ℓ`, and every prime ≤ 324 lies in `T(u)` (`mem_S_mul_of_le`). G6: noncommutativity from `PK.q.iota`; `EndDivision` needs NoCM | `modelG3G6_of_at` |
| 28 | `linkedTateData` | **UNSURE as stated** (pin: `FibreCtx`, and `G7Out`'s `rank End = 4` needs NoCM); after repair TRUE, SPECULATIVE | ∀ over all admissible `G7Data`, including `L'` wildly ramified at 2 beyond `U₀` (`[L':ℚ] ≤ D^{D E₀}·M(u)` allows `ℚ(ζ_{2^k})`, `k ~ D E₀ > U₀`). Not a refutation: every ℓ-adic datum is existential. Given `m = λμ` (`λ ∈ ℚ^×` by NoCM) and `β`, the prover can take `Tm = μ∘σ`, `β' = β/λ = β₀ψ` (`ψ² = χ/χ₀`, tame at odd `p`, bounded at 2), trivial on `G_{L'}`; `r = r⁰⊗ψ⁻¹` then has Glazer's ramification (§4). No twist attack on `∀ r₅ r₃`: `G8Out` fixes `r` | `linkedTateData_of_at` |
| 17 | `g9Glue` | **TRUE; not provable from its hypotheses** | `R10Weights` (Tate–Sen) is neither a hypothesis nor in the bundle's `r10`; `AbVarBaseChange` is glue | reduced, re-elaborated on G0Assemble's layer: `RvGP2.g9Glue` (`G9Bridge.AbVarBaseChange`, `G9Bridge.R10Weights`) (c10) |
| 18 | `g10Glue` (statement changed by g0-assemble) | **TRUE; not provable from its hypotheses** | the Betti argument needs Artin comparison (T12, from T35, T5, T26); not passed | **`g10Glue_of_conjTwist_new : ConjTwistNontrivial → G10Glue`** (c1) |
| 5 | `analyticUniformizationUnique` | **TRUE**; needs analytic input (complex-torus structure of `A(ℂ)`) | non-discrete `Λ`, `g ≠ dim A`, `dim A = 0`: all fine, since a holomorphic surjective hom `ℂ^g → A(ℂ)` is `exp∘D` with `D` linear surjective, and `T` with `D∘T = D'` works | none |
| 7 | `metrizationExists` | **TRUE**; rests on the uniformization leaf | the reduction needs `AnalyticUniformizationOfDim` (a leaf in neither bundle) and `JacDetNondegenerate` (glue) | reduced: `RvGP2.metrizationExists` (c6) |
| 11 | `thetaRatiosAlgebraic` | **TRUE**; leaf candidate (composite), needs human audit | `IsPeriodMatrix` (`Λ ≅ Ωℤ²+ℤ²`, `Ω ∈ 𝔥₂`) forces a principal polarization in a symplectic basis; algebraic over ℚ; `θ_{m₀} ≠ 0` required, so `x/0 = 0` cannot trivialize it; `IsUniformization` forces `dim A = 2` | none |
| 23 | `carayolR17` | **TRUE**; a published corollary (Carayol (A) plus Casselman, Chebotarev/Brauer–Nesbitt, duals, WD vs Serre–Tate), not the printed sentence | the `IsNewform` encoding is equivalent to the usual one | none |
| 15 | `burnsideAbsIrred` | **TRUE; proved here from Mathlib** (not a leaf) | W = 0: the hypothesis fails (irreducible needs nontrivial). Proof: Schur plus Jacobson density over `AlgebraicClosure F`, then a dimension count for the descent | **proved**: `RvGP2.burnsideAbsIrred` (c11) |
| 16 | `r14Det` | **TRUE**; weaker than published | arithmetic-Frobenius convention: the dual of Deligne's `ρ_f` has `det = ε'·χ_ℓ^{k−1}`; `ε` is only existential with finite image | none |
| 1 | `mulIsogeny` | **TRUE** leaf | default `intCast` of `End A` is `n • 1 = [n]`; `dim 0`: `[n] = id` | none |
| 2 | `rigidityHom` | **TRUE** leaf | Milne's rigidity needs `A` proper and geometrically integral, `B` separated, all supplied by `AbVar`; `IsMonHom` is the right target | none |
| 8 | `productMetrizationGeo` | **TRUE** | `IsProductModel` pins `𝒢P ≅ 𝒢₁ × 𝒢₂` over `𝓞_L`; multiplicativity holds with a 0-dimensional factor | reduced: `RvGP2.productMetrizationGeo` (`ProductLocalStructure`, `ProductHodgeLattice`) (c6) |
| 9 | `hodgeLineBaseChange` | **TRUE** | `IsBaseChangeOf` is an honest group iso `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`, so it never claims Néron models are stable | reduced over G0Assemble's `DefFaltings.AbVar`: `RvGP2.hodgeLineBaseChange` (four height-bc glue Props) (c7) |
| 19 | `g12Weight` | **TRUE** (conclusion ⇔ `k = 2`) | averaged `htMult` harmless for `G_{ℚ_p}` reps | reduced: `RvGP2.g12Weight` (`SenTwist`, `FiniteImageHT`, leaves outside the bundles) (c5) |
| 20 | `detTate` | **TRUE** | standard left Galois action checked (an inverse action would make it false) | reduced: `RvGP2.detTate` (weil-pairing's three leaves + bundle `t26`) (c5) |
| 3 | `finiteDescends` | **TRUE** | statement character-identical to fs1-descend's | **proved**: `RvGP2.finiteDescends` (c2) |
| 6 | `metrizationDimUnique` | **TRUE** | (none) | **proved**: `RvGP2.metrizationDimUnique` (c2) |
| 14 | `unramifiedSup` | **TRUE** | (none) | **proved**: `RvGP2.unramifiedSup` (c2) |
| 22 | `dirichletOfFinite` | **TRUE** | (none) | **proved from bundle `t.t17`**: `RvGP2.dirichletOfFinite` (c4) |
| 24 | `swanIndependent` | **TRUE** | G0Assemble L38177-38762 = kernel `LadicCond.lean` L180-765 (diff) | **proved**: `RvGP2.swanIndependent` (c3) |
| 25 | `swanIntegral` | **TRUE** | as 24 | **proved**: `RvGP2.swanIntegral` (c3) |
| 26 | `adaptedExists` | **TRUE** | as 24 | **proved**: `RvGP2.adaptedExists` (c3) |

Counts:
- **UNSURE as stated:** 6 (4, 10, 12, 13, 27, 28). All six are pin-dependent, all are repaired by
  the rebase, and the rebase is checked.
- **TRUE:** 21.
  - Proved here on G0Assemble's constants: 8 (3, 6, 14, 15, 22, 24, 25, 26).
  - Reduced here: 7 (7, 8, 9, 17, 19, 20, plus 18 to `ConjTwistNontrivial`).
  - True leaves or leaf candidates: 1, 2, 11, 16, 23.
  - True glue without a Lean check here: 5.

## 2. Lean checks (all VERIFIED: 0 errors, no `sorry`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`)

Set-up:
- `build_prefix.sh` compiles `scratch/h-decomposition/Leaves.lean` (post pin-apply, verbatim) to
  `olean/LPrefix.olean`: exit 0 in 603 s.
- `assemble.sh` builds `olean/TailBase.lean`: `import LPrefix`, g0-assemble's three extra imports,
  then g0-assemble's 18 part files, verbatim except parts/40_fibresimple.lean. There, the
  demonstration lemmas `r1fpProps_twistBy` and `fibreComTrivial_twisted` take
  `R1famProps ∧ R1univProps` for the relabeled Φ as an extra hypothesis.
- `ctail.sh TailBase.lean TailBase` gives exit 0 in 152 s. That includes
  `HSyn.gluePieces_of_gluePieces2` and `HSyn.sixContactMin_of_leaves2`; the earlier monolithic run is
  in `olean/Tail_out.txt`.
- Each check `checks/X.lean` compiles as `import TailBase` plus its body.

| check | content | result |
|---|---|---|
| c1_g10 | g10-odd `G10Odd.lean` L102-239 verbatim + `g10Glue_of_conjTwist_new` | exit 0, 47 s |
| c2_proved | fs1-descend, unram-tate `UnramSup.lean`, metrization `ExtLine.lean` + `part_dim.lean`; `RvGP2.finiteDescends`, `unramifiedSup`, `metrizationDimUnique` | exit 0, 40 s (first run lacked ExtLine) |
| c3_swan | swan's `All.lean` without imports and without its t-different copy (Leaves.lean already has `TDifferent`, `PkgI6.herbrandQuotient`; first run: 47 "already declared"); `RvGP2.swanIndependent`, `swanIntegral`, `adaptedExists` | exit 0, 29 s |
| c4_dirichlet | x1-dirichlet's `Dirichlet.lean` body with `open TSkolemKW.KW hiding Qbar GQ` (Leaves.lean's `TSkolemKW.KW` declares its own); `RvGP2.dirichletOfFinite t := … t.t17` | exit 0, 16 s |
| c5_g12det | g12-det's `Integrate.lean` minus its ModGalois copy and `part_integrate`; `RvGP2.detTate`, `RvGP2.g12Weight` | exit 0, 42 s |
| c6_metrization | metrization's ExtLine + parts (without `part_g0dim`); 7 off-route `heightAdditivity_of_metrization*` removed (they use `heightAdditivity_of_geo`, absent from G0Assemble); `RvGP2.metrizationExists`, `productMetrizationGeo` | exit 0, 10 s |
| c7_heightbc | height-bc's `Final.lean` with `open PkgI3 (AbVar)` removed; `RvGP2.hodgeLineBaseChange` | exit 0, 13 s |
| c8_fibrecover | fibre-cover's `FibreCover.lean` L16-17, L74-731, with `obtain ⟨-, -, -, hnat, -, -⟩` (six clauses); `RvGP2.fibreCoverExists` | exit 0, 12 s |
| c10_g9 | `ZInQKernel/Contrib/G9/*.lean` without its restated layers (I3Layer, I4Layer, Statement), with `open _root_.PkgI4…` added where the files' `namespace PkgI4…` shadows the root (first run: 101 errors, `modPMap` unknown); `RvGP2.g9Glue` | exit 0, 67 s |
| c11_burnside | `Burnside.lean` (Schur + Jacobson density over `AlgebraicClosure F`, dimension count) + `RvGP2.burnsideAbsIrred` | exit 0, 13 s |
| c12_bundle (`final/`) | imports c1-c11; `HSyn.GluePieces3` (15 fields), `gluePieces2_of_3`, `sixContactMin_of_leaves3` | exit 0, 23 s |
| c9_pin_transfer | `…At` forms generated by `gen_at.py` from the six fields' own text; `fibreCtx_transfer`, `rationalFibre_transfer`; the six `…_of_at` theorems | exit 0, 65 s |

Statement of the c9 theorems, with `Field` one of the six:

```lean
theorem Field_of_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ Φ₀ π₀} (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : FieldAt Y₀ Φ₀ π₀) : Field
```

`FieldAt` is the field's body with `(Y, Φ, π)` fixed. The proof moves the hypotheses `FibreCtx`,
`RationalFibre` and `FibreOver` along the comparison morphism `Y → Y₀`. For field 12 it also moves
the conclusion `RationalFibre` along `Y₀ → Y`. Both morphisms come from pin-apply's
`sameTripleMor_of_leaves`, which needs `R1univProps`, so this works only over the pinned prefix.

## 3. Recommendations (repairs)

1. **Regenerate G0Assemble.lean from the current `scratch/h-decomposition/Leaves.lean`**, using
   `scratch/rv-gluepieces2/parts/` (only 40_fibresimple differs). Two options:
   - add `Pin.MobiusGlue` to `GluePieces2`; or
   - restate fields 4, 10, 12, 13, 27 and 28 in their `…At` or ∃-form, in the style of pin-apply's
     `GluePiecesPin`.

   Either way, a prover then proves them for the genuine `Y₃` only. Before that change, the six
   fields should not be counted as provable glue.
2. Replace fields 3, 6, 14, 15, 24, 25 and 26 by the theorems, and field 22 by
   `X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic t.t17`. The code is in c2, c3, c4 and c11.
   With field 15 proved, the literature count goes down by one: g0-assemble's 63 becomes 62.
3. **`G9Glue`:** strengthen the bundle's `r10` with `R10Weights` (g9-derham F1), and make
   `AbVarBaseChange` a hypothesis or a named glue Prop.
4. **`G10Glue`:** adopt g10-odd's `G10GlueConcrete` hypotheses (`UniformizationExists`,
   `PkgI2.TorsionStructure`, `PkgI3.TateModuleFree`), and pass `t.t35 t.t5 t.t26` in `g8_g11`.
5. **Relabel as leaves:** the uniformization theorem behind fields 5 and 7
   (`AnalyticUniformizationOfDim`); also `SenTwist`, `FiniteImageHT` and weil-pairing's three leaves
   (fields 19, 20). None of these is in `ResearchLeaves` or `TextbookLeaves`. Mark field 23 as a
   "published corollary", and field 11 as a composite needing human audit.
6. **Optional, for `LinkedTateData`:** record `[L:ℚ] ≤ D` in `G7Data`. G4 proves it
   (`g4Out_of_kernelField`, `hdeg`). Then `L'` is tame at every `p > D`, and the proof of field 28
   no longer has to handle a hom-field `L` of unbounded wild ramification.

## 4. Notes on the three hardest fields

- **`linkedTateData` (28).** The data `Tm₅, c₅, ε₅, a₅, β₅, u₅` (and those at 3) are all chosen by
  the prover. The ∀ over `r₅, r₃` is pinned, because `G8Out` gives `r ⊕ r ≅ ρ` with `r`
  absolutely irreducible.
  - The only universal quantifier that could hurt is the one over `G7Data`.
  - `G7Data` bounds `[L':ℚ]` by `D^{D·E₀}·M(u)` (`heightQ`, `heightE₀ = 10(DG₀)²`, Height.lean
    L139-148), which is larger than `2^{U₀}` with `U₀ = 4(DG₀)²`. It puts no degree bound on `L`.
    So an admissible `L'` can contain `ℚ(ζ_{2^k})` with upper breaks above `U₀`.
  - The given `DescentDatum` `m` differs from the canonical `μ` by `λ_σ ∈ ℚ^×`: the centralizer of
    `𝒪` in `End⁰ = B` is ℚ, by NoCM. The given `β` satisfies `∂β = ε₀·∂λ` and `β² = χ`, so
    `β = β₀λψ` with `ψ` a Dirichlet character, `ψ² = χ/χ₀`.
  - The prover takes `Tm = μ∘σ`, `a ≡ 1`, `ε₅ = c` and `β' = β/λ = β₀ψ`. These are trivial on
    `G_{L'}`, since `λ = 1` on `G_L`.
  - Then `r = r⁰ ⊗ ψ⁻¹`. Since `ψ` is tame at odd `p` and of bounded conductor at 2, clauses (i) and
    (ii) of `G15RamWild` hold with Glazer's bound. Trace compatibility comes from common algebraic
    scalars through `j₅∘γ`, `j₃∘γ` (g14-trace).
  - Status: SPECULATIVE argument; it needs NoCM, hence the pin.
- **`fibreComTrivial`, `fibreQMPeriod`, `kernelFieldExists` (4, 10, 13).** rv-g0pieces' verdict
  stands for G0Assemble's copy. A refutation would need an explicit ℚ-isomorphism of finite étale
  fibres between a non-contact rational value and a rational CM value of π (or a bad-height value),
  and none is known. A proof would have to exclude every such isomorphism, and no method for that is
  known. The pinned rebase removes the question (c9).
- **`modelG3G6` (27).** The G3 half is true for every admissible datum. It needs no pin, because
  `IsQMModel` brings the level-3 object `PK`. The G6 half is exactly NoCM.

## 5. What was not done

- **No Lean check** was run for fields 1, 2, 5, 11, 16 and 23. These are leaves or
  analytic glue; the verdicts rest on reading (review notes) and the STANDARD references, whose
  locators are UNVERIFIED.
- **`MobiusGlue` is not proved here.** pin-apply names `origin/wip/mobius-glue` as the task that
  works on it.
