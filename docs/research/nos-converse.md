# nos-converse: the converse of Néron–Ogg–Shafarevich (`NOSProof.NOSConverseSep`), reduced along Serre–Tate's proof

Task nos-converse, 2026-11-16. Base wip/nos-proof `e9828e92`, merged origin/main `e41a7169`. Log:
`scratch/nos-converse/log.md`. Lean: `ZInQKernel/Contrib/OneProof/NOSConverseReduction.lean` (namespace `NOSConverse`;
the same text is `scratch/nos-converse/Reduction.lean`).

## Verdict

* **The target (`r7a` removed, −1, no new leaf) is not reachable from the open fields.** Two reasons, both
  VERIFIED by reading the Lean statements of every field of `OpenResearchLeaves26`, `OpenTextbookLeaves12`,
  `OpenAddedLeaves17` and `OpenGlue8`:
  1. *No field builds a model over a general DVR.* The only field that produces a scheme over a DVR is
     `neronSchemeExtensionExists` (BLR §1.4 Thm 3), and it is stated over `𝓞_L` for `L` a **number field**. The
     other Néron and SGA 7 fields (`raynaudSemistableSH`, `sga7_IX_3_3_SH`, `sga7_IX_3_5_ForwardGeom`,
     `neronBaseChangeStrictHenselization`) are conditional on a given Néron model. So `NOSConverseSep`, which
     quantifies over every field `K` (for example `K = ℂ((t))`), cannot follow from the bundles: nothing in them
     produces an abelian scheme over such an `O`. Any discharge of `r7a` over every field needs BLR §1.4 Thm 3 over
     an arbitrary DVR (`ReductSplit.NeronSchemeModelExistsDVR`, not a field) as a new leaf.
  2. *Even at number fields, the last step of Serre–Tate's proof is not in the bundles or in Mathlib*: "if the
     identity component of the special fibre of the Néron model is an abelian variety, then `A` has good reduction"
     (the properness criterion). It is isolated below as the leaf `AbelianReductionGood`.
* **What is proved (standard axioms only, VERIFIED by compiling):** the converse at number fields from the open
  fields plus one open glue Prop and one leaf. The glue Prop `InertiaFixedRational` is proved outright.

  ```
  nosConverseNF_of_two : NeronSchemeExtensionExists → NeronBaseChangeStrictHenselization →
    RaynaudSemistableSH → TorusRankZero → AbelianReductionGood → NOSConverseNF
  neronOggShafarevich_of_two : NeronSchemeModelExistsDVR → NeronBaseChangeStrictHenselization →
    RaynaudSemistableSH → TorusRankZero → AbelianReductionGood → PkgI2.NeronOggShafarevich.{0}
  ```

  The first three hypotheses of `nosConverseNF_of_two` are fields of the current bundles.
* **The narrowing asked for exists and is proved, but it does not give a discharge.** The one live consumer
  (`PkgI2.goodReduction_of_QM_rational3_of_alg`, LPrefix l. 814, QM surfaces over number fields) reads only the
  number-field form `NOSConverseNF` (`goodReduction_of_QM_rational3_of_algNF`, compiled). No weaker statement
  that the bundles supply serves it. The consumer has inertia-triviality only on `A[3^∞]` and needs good reduction,
  which makes `ℓ`-adic triviality hold for every `ℓ` downstream. No field gives the `ℓ`-independence (§4).
* **Recommendation: keep nos-proof's leaf `NOSConverseSep`**, a single printed theorem (Serre–Tate 1968 Thm 1,
  (c) ⇒ (a)). Through this file the autofold dry run gives `strict count: 34/11 on 45 -> 34/13 on 47` (refused:
  GLUE rises). The integrator may substitute the strictly weaker printed leaf `NOSConverseNF` if the consumer is
  rethreaded; `goodReduction_of_QM_rational3_of_algNF` is the replacement consumer for that.

`#discharges` (`scratch/nos-converse/Discharges.lean`, output in `Discharges-output.txt`; VERIFIED; lines for other
contributions omitted):

```
DISCHARGES [OpenResearchLeaves26.r7a] by NOSConverse.neronOggShafarevich_of_bar
  still assumes: [NOSConverse.NOSConverseBar]
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

`K` a field, `O` a DVR, `w` a valuation ring of `K̄` over `O`, `A/K` an abelian variety with inertia trivial on
`A(K̄)[m]` for infinitely many `m` invertible in `O`.

| step | content | supplier | status |
| --- | --- | --- | --- |
| 0 | pick `m ≥ 3` in the infinite set | `Set.Infinite.exists_gt` | proved |
| 1 | a Néron model `𝒩` of `A` over `O` | number fields: field `neronSchemeExtensionExists` with gt-blr's proved BLR 1.2/4 (`GapNeron.exists_neron_groupModelNF`). Any DVR: `ReductSplit.NeronSchemeModelExistsDVR` (BLR §1.4 Thm 3), **not a field** | NF: from a field |
| 2 | inertia-fixed `m`-torsion is rational over the inertia field `E` (whose valuation ring `w ∩ E` is the strict henselization, `GapSHPair.isSHSep_inertia`) | `InertiaFixedRational` | **proved here** |
| 3 | `𝒩 ⊗ O^sh` is a Néron model and is semistable, hence `𝒩` is semistable | fields `neronBaseChangeStrictHenselization`, `raynaudSemistableSH` (at `m ≥ 3`); `ReductGlue.isSemistable_bcDVR_iff` (proved) | from fields |
| 4 | the torus part of `𝒩⁰_{k̄}` is trivial (torsion count) | `TorusRankZero` | **open GLUE** |
| 5 | `𝒩⁰_{k̄}` abelian ⇒ good reduction | `AbelianReductionGood` | **open LEAF** (pending reading) |

The (a) ⇒ (b) ⇒ (c) directions were proved by nos-proof and are reused (`neronOggShafarevich_of_bar`).

## 2. The statements (all in `NOSConverseReduction.lean`)

* `NOSConverseBar`: the (c) ⇒ (a) half of `r7a` word for word (over `K̄ = AlgebraicClosure K`).
  `neronOggShafarevich_of_bar : NOSConverseBar → r7a` and `bar_of_neronOggShafarevich` (the converse of that) are
  proved, so `NOSConverseBar` is exactly the converse content of the field. `bar_of_sep : NOSConverseSep →
  NOSConverseBar` is proved too.
* `NOSConverseNF`: `NOSConverseBar` with `[NumberField K]`. It is a specialization (`nf_of_bar`), hence printed form
  (a consequence of Serre–Tate Thm 1).
* `HasAbelianIdentityComponent G` (a definition, for a group scheme `G` over a field): an open connected subgroup
  scheme `U ⊆ G` with `U` proper over `k`. For smooth `G` this is "`G⁰` is an abelian variety". It is a genuine
  definition with no invented structure.
* **`InertiaFixedRational`** (GLUE, **proved**: `inertiaFixedRational_proof`): for `m` invertible in `O`, a point of
  `A(K̄)[m]` fixed by the inertia group of `w` comes from `A(E)`, where `E = GapSHPair.inertiaField w`.
* **`TorusRankZero`** (GLUE, open): if `𝒩` is a semistable Néron model of `A` over `O` (in the bundles' sense
  `GroupModelO.IsSemistable`: the identity component of the geometric special fibre is an extension of an abelian
  variety by a split torus) and inertia is trivial on `A(K̄)[m]` for infinitely many `m` invertible in `O`, then the
  identity component of the geometric special fibre is an abelian variety.
* **`AbelianReductionGood`** (LEAF, open): if `𝒩` is a Néron model of `A` over the DVR `O` and the identity component
  of its geometric special fibre is an abelian variety, then `A` has good reduction (`PkgI2.HasGoodReduction`, the
  chain's definition).

### Ratings of the new statements

* `AbelianReductionGood`: **printed form, pending reading.** It is the last step of Serre–Tate's proof of Thm 1
  (§2). The statement "A has good reduction iff the identity component of the special fibre of the Néron model is
  an abelian variety" is standard: Serre–Tate §1, BLR §7.4, and the properness criterion for smooth separated group
  schemes of finite type over a DVR with connected proper special fibre, EGA IV₃ 15.7.10 / SGA 3 VI_B. All these
  locators are UNVERIFIED (no source on this host). Reading risks: (i) no exact print has been located; (ii) a print
  over the closed fibre `k` gives this `k̄`-form only together with descent of properness of `G⁰` along `k̄/k`
  (glue). It is true as stated: `𝒩⁰` is then an abelian scheme with generic fibre `A`. It is not vacuous, since the
  zero abelian variety satisfies it, and it is a consequence of the published equivalence, never stronger.
* `TorusRankZero`: **GLUE.** Its proof is Serre–Tate §2's count. Over `O^sh` the points of `A[m]` are rational
  (step 2). The Néron property gives `A(K^sh)[m] = 𝒩(O^sh)[m]`, and this injects into `𝒩_s(k̄)[m]` since `[m]` is
  étale on the smooth commutative group scheme `𝒩` (BLR §7.3 Lemma 2; PR #19 proves this only for abelian schemes).
  Next, `#𝒩_s(k̄)[m] ≤ #Φ · m^r · m^{2a}` (field `mumfordTorsionAlgClosed` for the abelian part, roots of unity for
  the torus, `Φ` the finite component group), and `a + r = g` (equidimensionality, field `groupSchemeEquidim`, and
  fibre dimension of smooth morphisms). Infinitely many `m` then force `r = 0`, and `𝒩⁰_{k̄} → B` is a flat
  surjective monomorphism, hence an isomorphism (Mathlib `Flat.isIso_of_surjective_of_mono`). The parts that are
  absent from Lean are the étaleness of `[m]` on smooth group schemes, the finiteness of `Φ` and the dimension
  formula `a + r = g`.
* `NeronSchemeModelExistsDVR` (existing def, TailZ7 l. 238): printed form (BLR §1.4 Thm 3 over any DVR; locator
  UNVERIFIED). Needed only for `r7a` over every field, not by the consumer.

## 3. What `InertiaFixedRational` needed (the proof)

`isInertia_of_fixes`: an automorphism `σ ∈ Aut(K̄/K)` that fixes the inertia field `E` pointwise lies in the
inertia group of `w`. Proof, in any characteristic:

* For `y ∈ w` separable over `K`, take a finite Galois `M ∋ y` (`GapSHPair.isFG_of`). Every element of the fixed
  field of the finite inertia group `inertM w M` lies in `E` (`mem_inertiaField_of_fixed`, straight from gt-shpair's
  definition of `E`). So `σ|_M` fixes that fixed field. By the finite Galois correspondence
  (`IntermediateField.fixingSubgroup_fixedField`), `σ|_M ∈ inertM w M`, that is, `σ y − y ∈ 𝔪_w`.
* For general `y ∈ w`, `y^{p^n}` is separable, and `(σ y − y)^{p^n} = σ(y^{p^n}) − y^{p^n} ∈ 𝔪_w`
  (`sub_mem_nonunits`).
* Hence `σ(w) ⊆ w` and `σ⁻¹(w) ⊆ w` (σ is in the decomposition group), and `σ` acts trivially on `κ(w)`.

Then reduct-b's `ReductB.fixedTorsionRational_inter` (Galois descent of torsion to an intermediate field, from `[m]`
étale, PR #19) gives the `E`-rational point. `torsion_rational_inertiaField` transports this to the hypothesis
form of `raynaudSemistableSH` for `A_E` over `Ē`, using `torsion_descends_etale` and an `E`-embedding `K̄ → Ē`.

## 4. The consumer and the narrowing

The one live use of the converse (nos-proof §3, from the closure scan) is LPrefix l. 856, inside
`PkgI2.goodReduction_of_QM_rational3_of_alg` (`[NumberField K]`, QM surface for `(2, −3)`, `A[3]` rational,
`3 ∈ O^×`). It reaches the chain through `LeafQM.AV.QML3.goodReduction`, used by `qmModelG3_of` (TailF l. 2293) and
`good_of_QML3` (TailC l. 5947). Both turn `HasGoodReduction` into `ℓ`-adic triviality of inertia **for every `ℓ`**
(`GoodRedG3Bridge`, `kernelField_of_model`).

* *Number fields only*: proved. `goodReduction_of_QM_rational3_of_algNF` is the consumer with `NOSConverseNF` in
  place of `r7a`, with the proof otherwise verbatim (compiles; an `example` checks that it specializes back).
  `NOSConverseNF` is not supplied by the bundles, though. It needs `TorusRankZero` and `AbelianReductionGood`
  (§1). A fold through it would be a rethread (the semantic-prune recipe: thread a new binder through LPrefix,
  TailC and TailF), giving `34/11 → 33/13`.
* *Good reduction from trivial inertia on `T_ℓ` for every `ℓ`*: not useful. The consumer only has `ℓ = 3` (and
  `ℓ = 2` by `QuatUnipotentTrivial`). For `ℓ ∤ 6`, `B ⊗ ℚ_ℓ ≅ M₂(ℚ_ℓ)` has nonzero square-zero elements, so the
  fields (`(σ − 1)² = 0` from `raynaudSemistableSH` with `sga7_IX_3_5_ForwardGeom`) do not give `σ = 1`.
  `ℓ`-independence is the content of the converse, and no field states it. `GrothendieckMonodromy` and
  `RaynaudCriterion` give only unipotence; `charPolyIndepOfEllAlgClosed` concerns endomorphisms, not Galois
  elements.
* *An integral Shimura model* would give good reduction directly, by properness of the moduli scheme, but the field
  `shimuraIntegralModelRep` was pruned at sgr-fold (TailZ39).

## 5. For the integrator

* **Do not fold** `scratch/nos-converse/autofold.json`. Its dry run is
  `strict count: 34/11 on 45 -> 34/13 on 47; strictest 34/11 -> 34/13` and autofold refuses it
  (`autofold-dryrun.txt`). The spec is kept to record the trade.
* Reusable results: `NOSConverse.isInertia_of_fixes` (`Aut(K̄/E) ⊆ I_w` for gt-shpair's inertia field, any
  characteristic) and `inertiaFixedRational_proof`. The pair `goodReduction_of_neron` / `nosConverseNF_of_two`
  becomes a discharge as soon as `TorusRankZero` is proved and `AbelianReductionGood` is read.
* Proposed `docs/research/locators.md` row: `NOSConverse.AbelianReductionGood | Serre–Tate 1968 §1–§2; BLR §7.4;
  EGA IV₃ 15.7.10 | UNVERIFIED | pending reading (k vs k̄)`.

## 6. Files

* `ZInQKernel/Contrib/OneProof/NOSConverseReduction.lean` (lake build, 20 s, standard axioms).
* `scratch/nos-converse/`: `log.md`; `Reduction.lean` (the same content, compiled with `lake env lean`);
  `Discharges.lean` and `Discharges-output.txt`; `autofold.json` and `autofold-dryrun.txt`; `Probe.lean`.
