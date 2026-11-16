# nos-converse: the converse of Néron–Ogg–Shafarevich (`NOSProof.NOSConverseSep`), reduced along Serre–Tate's proof

Task nos-converse, 2026-11-16. Base wip/nos-proof `e9828e92`, merged origin/main `e41a7169`. Log:
`scratch/nos-converse/log.md`. Lean: `ZInQKernel/Contrib/OneProof/NOSConverseReduction.lean` (namespace
`NOSConverse`). The same declarations are in `scratch/nos-converse/Reduction.lean`.

## Verdict

* **The target (`r7a` removed, −1, no new leaf) is not reachable from the open fields.** Both reasons were VERIFIED
  by reading the Lean statement of every field of `OpenResearchLeaves26`, `OpenTextbookLeaves12`,
  `OpenAddedLeaves17` and `OpenGlue8`.
  1. *No field builds a model over a general DVR.* The only field that produces a scheme over a DVR is
     `neronSchemeExtensionExists` (BLR §1.4 Thm 3), and it is stated over `𝓞_L` for `L` a **number field**. The
     other Néron and SGA 7 fields (`raynaudSemistableSH`, `sga7_IX_3_3_SH`, `sga7_IX_3_5_ForwardGeom`,
     `neronBaseChangeStrictHenselization`) are conditional on a Néron model that is already given.
     `NOSConverseSep` quantifies over every field `K` (for example `K = ℂ((t))`), and nothing in the bundles
     produces an abelian scheme over such an `O`. So a discharge of `r7a` over every field needs BLR §1.4 Thm 3 over
     an arbitrary DVR (`ReductSplit.NeronSchemeModelExistsDVR`, not a field) as a new leaf.
  2. *Even at number fields, inputs of Serre–Tate's proof are missing from the bundles and from Mathlib.* One is
     "if the identity component of the geometric special fibre of the Néron model is an abelian variety, then `A`
     has good reduction" (a properness criterion; leaf `AbelianReductionGood`). The others are two geometric facts
     about Néron models used in the torsion count (glue, §2).
* **What is proved (standard axioms, VERIFIED by `lake build` and `#print axioms`):** `r7a`, and its converse at
  number fields, from the open fields plus the pieces of Serre–Tate's proof that no field supplies. Along the way
  five pieces are **proved outright**: `InertiaFixedRational`, `ComponentIndexBound`, `SemiAbelianTorsionBound`,
  `RankZeroAbelian` and `NeronSpecialFibreComm` (§3).

  ```
  nosConverseNF_of_open : NeronSchemeExtensionExists → NeronBaseChangeStrictHenselization →
    RaynaudSemistableSH → MumfordTorsionAlgClosed →
    TorsionInjectsSpecialFibre → DimensionRelation → AbelianReductionGood → NOSConverseNF
  neronOggShafarevich_of_open : NeronSchemeModelExistsDVR → (the same six) → PkgI2.NeronOggShafarevich.{0}
  ```

  The first four hypotheses of `nosConverseNF_of_open` are fields of the current bundles. The last three are open:
  two GLUE and one LEAF.
* **The narrowing asked for exists and is proved, but it gives no discharge.** The one live consumer
  (`PkgI2.goodReduction_of_QM_rational3_of_alg`, LPrefix l. 814, QM surfaces over number fields) reads only the
  number-field form `NOSConverseNF` (`goodReduction_of_QM_rational3_of_algNF`, compiled). No weaker statement that
  the bundles supply serves it: the consumer has inertia-triviality only on `A[3^∞]` and needs good reduction,
  hence `ℓ`-adic triviality for every `ℓ` downstream, and no field gives that `ℓ`-independence (§4).
* **Recommendation: keep nos-proof's leaf `NOSConverseSep`**, one printed theorem (Serre–Tate 1968 Thm 1,
  (c) ⇒ (a)). Through this file the autofold dry run gives `strict count: 34/11 on 45 -> 34/14 on 48`, and autofold
  refuses it because GLUE rises. If the consumer is rethreaded, the integrator may instead use the strictly weaker
  printed leaf `NOSConverseNF`; `goodReduction_of_QM_rational3_of_algNF` is the replacement consumer.

`#discharges` (`scratch/nos-converse/Discharges.lean`; output in `Discharges-output.txt`; VERIFIED; lines for other
contributions omitted):

```
DISCHARGES [OpenResearchLeaves26.r7a] by NOSConverse.neronOggShafarevich_of_bar
  still assumes: [NOSConverse.NOSConverseBar]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.r7a] by NOSConverse.neronOggShafarevich_of_open
  still assumes: [ReductSplit.NeronSchemeModelExistsDVR,
 GapSHPair.NeronBaseChangeStrictHenselization,
 ReductGlue.RaynaudSemistableSH,
 AvSplit.MumfordTorsionAlgClosed,
 NOSConverse.TorsionInjectsSpecialFibre,
 NOSConverse.DimensionRelation,
 NOSConverse.AbelianReductionGood]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.r7a] by NOSConverse.neronOggShafarevich_of_two
  still assumes: [ReductSplit.NeronSchemeModelExistsDVR,
 GapSHPair.NeronBaseChangeStrictHenselization,
 ReductGlue.RaynaudSemistableSH,
 NOSConverse.TorusRankZero,
 NOSConverse.AbelianReductionGood]
  axioms: [propext, Classical.choice, Quot.sound]
```

## 1. Serre–Tate's proof, step by step, against the open fields

Setting: `K` a field, `O` a DVR, `w` a valuation ring of `K̄` over `O`, and `A/K` an abelian variety such that
inertia is trivial on `A(K̄)[m]` for infinitely many `m` invertible in `O`.

| step | content | supplier | status |
| --- | --- | --- | --- |
| 0 | pick `m ≥ 3` in the infinite set | `Set.Infinite.exists_gt` | proved |
| 1 | a Néron model `𝒩` of `A` over `O` | number fields: field `neronSchemeExtensionExists` with gt-blr's proved BLR 1.2/4 (`GapNeron.exists_neron_groupModelNF`). Any DVR: `ReductSplit.NeronSchemeModelExistsDVR` (BLR §1.4 Thm 3), **not a field** | NF: from a field |
| 2 | inertia-fixed `m`-torsion is rational over the inertia field `E`; `w ∩ E` is the strict henselization (`GapSHPair.isSHSep_inertia`) | `InertiaFixedRational` | **proved here** |
| 3 | `𝒩 ⊗ O^sh` is a semistable Néron model, so `𝒩` is semistable | fields `neronBaseChangeStrictHenselization` and `raynaudSemistableSH` (at `m ≥ 3`); `ReductGlue.isSemistable_bcDVR_iff` (proved) | from fields |
| 4a | `A(K̄)[m] ↪ 𝒩_{k̄}(k̄)[m]` | `TorsionInjectsSpecialFibre` | **open GLUE** |
| 4b | `#𝒩_{k̄}(k̄)[m] ≤ c · #U(k̄)[m]` (`U` the semi-abelian identity component) | `ComponentIndexBound` (`componentIndexBound_proof`) | **proved here** |
| 4c | `#U(k̄)[m] ≤ m^r · m^{2a}` | `semiAbelianTorsionBound_of`, from the field `mumfordTorsionAlgClosed` | **proved here** |
| 4d | `a + r ≤ g` | `DimensionRelation` | **open GLUE** |
| 4e | `#A(K̄)[m] = m^{2g}` | `AvSplit.torsionStructure_of_mumford` (field `mumfordTorsionAlgClosed`) | proved (tree) |
| 4f | the count forces `r = 0` | `torusRankZero_of_count` | **proved here** |
| 4g | `r = 0` ⇒ `U ≅ B`, so `U` is proper | `rankZeroAbelian_proof` | **proved here** |
| 4h | `𝒩` is commutative (used in 4c) | `neronSpecialFibreComm_proof` | **proved here** |
| 5 | `𝒩⁰_{k̄}` abelian ⇒ good reduction | `AbelianReductionGood` | **open LEAF** (pending reading) |

nos-proof proved (a) ⇒ (b) ⇒ (c); this file reuses them in `neronOggShafarevich_of_bar`.

## 2. The statements (all in `NOSConverseReduction.lean`)

* `NOSConverseBar`: the (c) ⇒ (a) half of `r7a`, word for word (over `K̄ = AlgebraicClosure K`). Proved:
  `neronOggShafarevich_of_bar : NOSConverseBar → r7a`, `bar_of_neronOggShafarevich` (its converse) and
  `bar_of_sep : NOSConverseSep → NOSConverseBar`.
* `NOSConverseNF`: `NOSConverseBar` with `[NumberField K]`, a specialization (`nf_of_bar`), hence printed form.
* `HasAbelianIdentityComponent G` (definition): an open connected subgroup scheme `U ⊆ G` that is proper over the
  base field. For smooth `G` this is "`G⁰` is an abelian variety".
* `SemiAbelianRank G U inc B π r` (definition): the clauses of the bundles' `HasSemiAbelianIdentityComponent` with
  `U, B, π, r` fixed (`hasSemiAbelian_iff`).
* **`TorsionInjectsSpecialFibre`** (GLUE, open): for a Néron model `𝒩` over `O` and `m` invertible in `O`, the
  inertia-fixed points of `A(K̄)[m]` inject into the `m`-torsion `k̄`-points of the geometric special fibre. Proof
  route (STANDARD): such points are rational over `K^sh` (step 2), `A(K^sh) = 𝒩(O^sh)` by the Néron property, and
  reduction `𝒩(O^sh)[m] → 𝒩(k̄)[m]` is injective because `𝒩[m]` is étale and separated (BLR §7.3 Lemma 2; PR #19
  proves `[m]` étale only for abelian schemes). Missing from Lean: `[m]` étale on a smooth group scheme, which
  needs the fibrewise flatness criterion.
* **`ComponentIndexBound`** (GLUE, **proved**: `componentIndexBound_proof`): an open subgroup `U` of the geometric
  special fibre `G` of a Néron model has `#G(k̄)[m] ≤ c · #U(k̄)[m]` for a fixed `c`.
* **`DimensionRelation`** (GLUE, open): for semi-abelian identity component data `(U, B, r)` on the geometric special
  fibre, `dim B + r ≤ dim A` (equality holds; only `≤` is used), both finite. Proof route: `dim U = dim A`
  (fibre dimension of the smooth `𝒩` along the identity section; field `groupSchemeEquidim`, infra-smooth-dim), and `dim U = dim B + r` (flat surjection
  with fibres `𝔾_m^r`). Missing from Lean: dimension of fibres of flat morphisms.
* **`AbelianReductionGood`** (LEAF, open): if `𝒩` is a Néron model of `A` over the DVR `O` and the identity component
  of its geometric special fibre is an abelian variety, then `A` has good reduction (`PkgI2.HasGoodReduction`).

### Ratings of the new statements

* `AbelianReductionGood`: **printed form, pending reading.** It is the last step of Serre–Tate's proof of Thm 1
  (§2), and the standard statement is "`A` has good reduction iff the identity component of the special fibre of
  the Néron model is an abelian variety". Sources, all UNVERIFIED (no source on this host): Serre–Tate §1; BLR
  §7.4; the properness criterion for smooth separated group schemes of finite type over a DVR with connected proper
  special fibre, EGA IV₃ 15.7.10 / SGA 3 VI_B. Reading risks: (i) no exact print has been located; (ii) a print over
  the closed fibre `k` gives this `k̄`-form only together with descent of properness of `G⁰` along `k̄/k` (glue).
  The statement is true: `𝒩⁰` is then an abelian scheme with generic fibre `A`. It is not vacuous, since the zero
  abelian variety satisfies it. It is a consequence of the published equivalence, never stronger.
* `TorsionInjectsSpecialFibre`, `DimensionRelation`: **GLUE** (consequences of standard
  facts about Néron models, BLR §7.3 and §9.2; no single print). Each is true as stated and none is vacuous: each
  has content whenever a Néron model exists.
* `NeronSchemeModelExistsDVR` (existing def, TailZ7 l. 238): printed form (BLR §1.4 Thm 3 over any DVR; locator
  UNVERIFIED). It is needed only for `r7a` over every field, not by the consumer.

## 3. What is proved here

* **`isInertia_of_fixes`** (any characteristic): an automorphism `σ ∈ Aut(K̄/K)` that fixes gt-shpair's inertia
  field `E` pointwise lies in the inertia group of `w`.
  * For `y ∈ w` separable, take a finite Galois `M ∋ y`. The fixed field of `inertM w M` lies in `E`
    (`mem_inertiaField_of_fixed`), so by the finite Galois correspondence `σ|_M ∈ inertM w M`, i.e.
    `σ y − y ∈ 𝔪_w`.
  * For general `y`, `y^{p^n}` is separable and `(σ y − y)^{p^n} = σ(y^{p^n}) − y^{p^n}`.
  * Hence `σ` lies in the decomposition group and acts trivially on `κ(w)`.

  With reduct-b's Galois descent of torsion (`ReductB.fixedTorsionRational_inter`, `[m]` étale from PR #19), this
  gives **`inertiaFixedRational_proof`**. `torsion_rational_inertiaField` puts it in the hypothesis form of
  `raynaudSemistableSH` for `A_E`.
* **`semiAbelianTorsionBound_of`** (from the field `mumfordTorsionAlgClosed`): `U(k)[m]` injects into
  `B(k)[m] × μ_m(k)^r` (fix a preimage in each fibre and take the torus coordinates of the difference; the kernel of
  `U → B` is the image of the injective `e`). Mumford gives `#B(k)[m] = m^{2a}`, and `#μ_m ≤ m` (Mathlib
  `card_rootsOfUnity`).
* **`rankZeroAbelian_proof`**: with `r = 0`, `π : U → B` has trivial kernel on all `R`-points, so it is a
  monomorphism of schemes (checked on affine opens). It is flat, surjective and locally of finite presentation, so
  it is an open immersion (Mathlib `IsOpenImmersion.of_flat_of_mono`), hence an isomorphism, and `U` is proper.
* **`isCommMonObj_neron`, `neronSpecialFibreComm_proof`**: a Néron model of a commutative `A` is commutative. On the
  smooth `𝒩 ×_O 𝒩`, `fst · snd` and `snd · fst` have the same generic fibre (`gen` is a homomorphism into the
  commutative `A`; Mathlib `Functor.map_mul`), so they are equal by the Néron property. Base change is braided
  (`Functor.isCommMonObj_obj`).
* **`index_bound`, `componentIndexBound_proof`**: for a commutative quasi-compact group scheme `G` locally of finite
  type over an algebraically closed `k` and an open subgroup `U`, `U(k)` has finite index in `G(k)`. The left
  translates `τ_x = lift(x ∘ str, 𝟙) ≫ μ` give open sets `τ_x⁻¹(U)`. They cover the closed points: every closed point
  is a `k`-point (Mathlib `pointOfClosedPoint`) and lies in its own translate. So they cover `G`, since a nonempty
  closed complement would contain a closed point (`IsClosed.exists_closed_singleton`). Finitely many suffice
  (compactness). Each coset meets `G(k)[m]` in at most `#U(k)[m]` points (translate by a point of the coset;
  commutativity).
* **`torusRankZero_of_count`**: from 4a–4g, `m^{2g} ≤ c · m^{r+2a}` for infinitely many `m`, so `2g ≤ r + 2a`;
  with `a + r ≤ g` this forces `r = 0`.

## 4. The consumer and the narrowing

The one live use of the converse (nos-proof §3, closure scan) is LPrefix l. 856, inside
`PkgI2.goodReduction_of_QM_rational3_of_alg` (`[NumberField K]`, a QM surface for `(2, −3)`, `A[3]` rational,
`3 ∈ O^×`). It reaches the chain through `LeafQM.AV.QML3.goodReduction`, used by `qmModelG3_of` (TailF l. 2293)
and `good_of_QML3` (TailC l. 5947). Both turn `HasGoodReduction` into `ℓ`-adic triviality of inertia **for every
`ℓ`** (`GoodRedG3Bridge`, `kernelField_of_model`).

* *Number fields only*: proved. `goodReduction_of_QM_rational3_of_algNF` is the consumer with `NOSConverseNF` in
  place of `r7a`, and the rest of its proof is verbatim. It compiles, and an `example` checks that it specializes
  back. The bundles do not supply `NOSConverseNF`, though (§1). A fold through it would be a rethread: thread a new
  binder through LPrefix, TailC and TailF, following the semantic-prune recipe. That fold gives `34/11 → 33/14`
  through this file, or `34/11 → 34/11` with `NOSConverseNF` as a printed leaf in place of `NOSConverseSep`.
* *Good reduction from trivial inertia on `T_ℓ` for every `ℓ`*: not useful. The consumer only has `ℓ = 3` (and
  `ℓ = 2` by `QuatUnipotentTrivial`). For `ℓ ∤ 6`, `B ⊗ ℚ_ℓ ≅ M₂(ℚ_ℓ)` has nonzero square-zero elements. The
  fields give only `(σ − 1)² = 0` (`raynaudSemistableSH` with `sga7_IX_3_5_ForwardGeom`), not `σ = 1`.
  `ℓ`-independence is the content of the converse, and no field states it: `GrothendieckMonodromy` and
  `RaynaudCriterion` give only unipotence, and `charPolyIndepOfEllAlgClosed` is about endomorphisms, not Galois
  elements.
* *An integral Shimura model* would give good reduction directly, by properness of the moduli scheme, but the field
  `shimuraIntegralModelRep` was pruned at sgr-fold (TailZ39).

## 5. For the integrator

* **Do not fold** `scratch/nos-converse/autofold.json`. Its dry run gives
  `strict count: 34/11 on 45 -> 34/14 on 48; strictest 34/11 -> 34/14`, and autofold refuses it
  (`autofold-dryrun.txt`). The spec is kept as a record of the trade.
* Reusable results:
  * `NOSConverse.isInertia_of_fixes` (`Aut(K̄/E) ⊆ I_w`) and `inertiaFixedRational_proof`;
  * `isCommMonObj_neron` (Néron models of abelian varieties are commutative);
  * `semiAbelianTorsionBound_of` and `rankZeroAbelian_proof` (semi-abelian varieties over `k̄`);
  * `index_bound` (open subgroups of quasi-compact group schemes over `k̄` have finite index on `k̄`-points).
* `nosConverseNF_of_open` becomes a discharge (after a rethread) once the two glue Props are proved and
  `AbelianReductionGood` is read.
* Proposed `docs/research/locators.md` row: `NOSConverse.AbelianReductionGood | Serre–Tate 1968 §1–§2; BLR §7.4;
  EGA IV₃ 15.7.10 | UNVERIFIED | pending reading (k vs k̄)`.

## 6. Files

* `ZInQKernel/Contrib/OneProof/NOSConverseReduction.lean` (`lake build` 14–20 s, standard axioms).
* `scratch/nos-converse/`:
  * `log.md`;
  * `Reduction.lean` (the same declarations, compiled with `lake env lean`);
  * `Discharges.lean` and `Discharges-output.txt`;
  * `autofold.json` and `autofold-dryrun.txt`;
  * `Probe.lean`.
