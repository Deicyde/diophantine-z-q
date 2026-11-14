# reduct-split: the reduction-of-abelian-varieties GLUE fields split into published forms

Task reduct-split, 2026-11-14. Base 5da857b0 (wip/w59). New Lean: `scratch/reduct-split/Reduction.lean` (one file,
namespace `ReductSplit`, imports only kernel modules; no `sorry`, no `axiom`; every row theorem depends on
`[propext, Classical.choice, Quot.sound]`, VERIFIED by `#print axioms` at the end of the file). Results log:
`scratch/reduct-split/log.md`. Nothing under `ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled or read in a file; **STANDARD** = published, with a reference; **SPECULATIVE** = a
judgement; **UNVERIFIED** = a theorem number recalled without a source (no network on this host; I could not read
SGA 7, Serre–Tate, BLR, Faltings, Raynaud or Milne, so every locator below is UNVERIFIED unless `locators.md` read it).

## 1. Main result

Seven of the eight rows are now Lean theorems from published-form leaves; t10 is not split. Leaves are stated in
printed form, or as a specialization read off the display, over genuine definitions. **Three rows use no glue at all**
(r7b, r8, and r6 over perfect fields). Every glue step found along the way that is commutative algebra or
point-counting was proved in Lean. What remains is four named glue Props, all local-to-global algebraic geometry or
étale descent in characteristic `p`, plus t10.

* **r7b `PkgI2.SerreTatePotentialGood`: done.** `serreTatePotentialGood_final : SerreTateThm2 →
  AvSplit.MumfordTorsionAlgClosed → PkgI2.SerreTatePotentialGood.{0}`. The leaves are Serre–Tate Thm 2 as printed (the
  image of inertia in `End(T_ℓ A)` is finite) and Mumford §4, which is already a bundle leaf.
* **r8 `PkgI2.GrothendieckMonodromy`: done.** `grothendieckMonodromy_final'` from SGA 7 IX 3.6 (at every place of `K'`
  over `O`), SGA 7 IX 3.5 (semistable ⇒ `(σ-1)² = 0` on `T_ℓ`), Néron's existence theorem over a DVR (BLR 1.4/3), and
  Mumford §4. The step "a valuation ring of a finite extension over a DVR is a DVR" (the fundamental inequality
  `e ≤ n`) is proved: `dvrFiniteExtension`.
* **r6 `PkgI2.RaynaudCriterion`: done over perfect fields.** `raynaudCriterion_final'` from Raynaud's criterion
  (SGA 7 IX 4.7, hypothesis "the points of order `m` are rational over `K`"), SGA 7 IX 3.5, BLR 1.4/3 and Mumford §4,
  plus **one glue, `FixedTorsionRationalImperfect`**. The glue is needed only for an **imperfect** `K`: there a
  Galois-fixed point of `A(K̄)[m]` must still be shown `K`-rational, which needs `A[m]` étale. The perfect case is proved
  (`exists_rational_of_fixed`), so in characteristic 0, the only case the project uses, r6 rests on published-form
  leaves only.
* **SS1 `HeightSplit.SemistableReductionThm` and SS3 `HeightSplit.SemistablePersists`**
  (`semistableReductionThm_final`, `semistablePersists_final`): from the **local** printed theorems SGA 7 IX 3.6, 3.3
  (persistence) and BLR 1.4/3, plus the glue `SemistableLocalGlobal` (and `SemistableAlmostAll` for SS1). The rest is
  proved in Lean: finitely many bad places, the compositum in `K̄`, comaps of discrete valuation rings
  (`dvrComapFinite`), and `(A_{K'})_L ≅ A_L` as group schemes.
* **SS2 `HeightSplit.SemistableNeronBaseChange`** (`semistableNeronBaseChange_of_leaves`): the local printed form
  (SGA 7 IX 3.3, second assertion) is stated as the leaf `IdentityComponentBaseChangeDVR`. The global content
  (identity component over `𝓞_L`, gluing) stays in the glue `SemistableNeronBaseChangeLocalGlobal`, so this row is only
  **partly** split.
* **`faltingsLemma5BC`** (`faltingsLemma5BC_final : HeightSplit.FaltingsLemma5 → HeightSplit.FaltingsLemma5BC`):
  reduced, with no glue, to the base-field form `HeightSplit.FaltingsLemma5` (A, B over the field over which the
  Néron models live). Two steps are proved:
  - the encoding: a model of `A_L` in `GroupModel A L`, as a model of `A_L/L`, keeps its Néron property, its
    semistability and its **height** (`gmTransport_*`);
  - `deg φ_L = deg φ` (`isogenyBaseChangeDeg`, by descent of kernel points).

  The base-field form is still a consequence of two printed results, Faltings' Lemma 5 (an identity with a `s^*Ω¹`
  correction term) and Raynaud's bound on that term. Neither can be stated over the kernel's objects (§4).
* **t10 `T10Etale.T10_TateDuality`: not split** (§4). The printed theorem is about étale ℓ-adic cohomology. Mathlib
  4.35 has only the pro-étale groups, with no comparison, and the Galois equivariance is a naturality statement that is
  not printed anywhere.

The bundle form is `rows_of_leaves (l : ReductLeaves) (g : ReductGlue) (hF5 : HeightSplit.FaltingsLemma5)`. It proves
all seven rows from eight published-form leaves (`ReductLeaves`) and four glue Props (`ReductGlue`). No row statement
was found false or vacuous. Reading risks are listed in §5: SGA 7 IX 4.7 may be printed over a strictly henselian base,
and Serre–Tate may assume a complete `K`.

## 2. Table

Names are in `scratch/reduct-split/Reduction.lean`, namespace `ReductSplit`. "Old form" is leaf-fold8's strict kind.

| row | old form | new leaves (published form, source) | new glue (status) | Lean name of the proof |
|---|---|---|---|---|
| r6 `PkgI2.RaynaudCriterion.{0}` | GLUE (c), SGA 7 IX 4.7 + 3.5 | `RaynaudSemistable` (SGA 7 IX Prop. 4.7: `m ≥ 3` invertible in `O`, `A[m]` rational over `K` ⇒ every Néron model over `O` semistable); `SemistableUnipotent` (SGA 7 IX Prop. 3.5, "⇒": semistable ⇒ `(σ-1)²=0` on `T_ℓ` for `σ` in inertia; `Ω` any algebraic closure); `NeronSchemeModelExistsDVR` (BLR §1.4 Thm 3 over a DVR, scheme form); bundle leaf `MumfordTorsionAlgClosed` | `FixedTorsionRationalImperfect` (open, imperfect `K` only; perfect case proved) | `raynaudCriterion_final'` |
| r7b `PkgI2.SerreTatePotentialGood.{0}` | GLUE (c), Serre–Tate Thm 2 | `SerreTateThm2` (Serre–Tate 1968 Thm 2: potential good reduction ⟺ `ρ_ℓ(I)` finite in `End(T_ℓ A)`); `MumfordTorsionAlgClosed` | none (`TorsionFieldOfDefinition` proved) | `serreTatePotentialGood_final` |
| r8 `PkgI2.GrothendieckMonodromy.{0}` | GLUE (c), SGA 7 IX 3.6 | `SemistableReductionDVR` (SGA 7 IX Thm 3.6: finite `K' ⊆ K̄` with `A_{K'}` semistable at every place over `O`); `SemistableUnipotent`; `NeronSchemeModelExistsDVR`; `MumfordTorsionAlgClosed` | none (`DVRFiniteExtension` proved) | `grothendieckMonodromy_final'` |
| `semistableReductionThm` (SS1) | GLUE (c), SGA 7 IX 3.6 global | `SemistableReductionDVR`; `SemistablePersistsDVR` (SGA 7 IX Prop. 3.3, first assertion, finite extensions); `NeronSchemeModelExistsDVR` | `SemistableLocalGlobal`, `SemistableAlmostAll` (open); `DVRComapFinite` proved | `semistableReductionThm_final` |
| `semistableNeronBaseChange` (SS2) | GLUE (c), SGA 7 IX 3.3 | `IdentityComponentBaseChangeDVR` (SGA 7 IX Prop. 3.3, second assertion, weakened to "open immersion `𝒩⁰ ×_O O' → 𝒩'`") | `SemistableNeronBaseChangeLocalGlobal` (open; carries the global content), `SemistableLocalGlobal` | `semistableNeronBaseChange_of_leaves` |
| `semistablePersists` (SS3) | GLUE (c), SGA 7 IX 3.3 global | `SemistablePersistsDVR`; `NeronSchemeModelExistsDVR` | `SemistableLocalGlobal` (open) | `semistablePersists_final` |
| `faltingsLemma5BC` | GLUE (c), Faltings Lemma 5 / Raynaud | `HeightSplit.FaltingsLemma5` (kernel def in TailY: Lemma 5 in the semistable inequality form, over the field of the models; still a consequence of Lemma 5 + Raynaud, Astérisque 127 VII Cor. 2.1.3) | none (encoding and `IsogenyBaseChangeDeg` proved) | `faltingsLemma5BC_final` |
| t10 `T10Etale.T10_TateDuality` | GLUE (c), Milne 15.1 | not split (§4) | — | — |

Exact displays. Where a field already *is* a printed statement over our definitions: none of the eight is literally a
display. The nearest is SS3, which is SGA 7 IX 3.3's persistence statement globalized over `𝓞_L`. The left side of
`SerreTateThm2` is the row's left side unchanged; it is Serre–Tate's definition of potential good reduction.

For leaf-fold integration (SPECULATIVE count): the 7 split rows, previously 7 strict GLUE (c) fields, become
* the 8 leaves of `ReductLeaves` (7 new published-form leaves plus the existing `MumfordTorsionAlgClosed`);
* 4 project-glue Props;
* `HeightSplit.FaltingsLemma5`, still (c).

## 3. Definitions introduced (genuine, over Mathlib/kernel objects)

* `GroupModelO A O`: the kernel's `GroupModel` over a valuation ring `O ⊆ K` instead of `𝓞_L`. It is a smooth,
  separated, quasi-compact group scheme with a group isomorphism `𝒩_K ≅ A`. `GroupModelO.IsNeronModel` is the Néron
  mapping property for smooth `O`-schemes (BLR §1.2 Def. 1).
* `geomSpecialFibre 𝒩 = 𝒩 ×_O κ̄`, with `κ̄ = AlgebraicClosure (ResidueField O)`. `GroupModelO.IsSemistable` is
  height-split's `HasSemiAbelianIdentityComponent` of it: the identity component is an extension of an abelian variety
  by a split torus, which is SGA 7 IX Déf. 2.2/3.2 read over `κ̄` (UNVERIFIED locator).
* `SemistableNeronModels A O` ("every Néron model is semistable") is the **conclusion** form, used by 3.6, 3.3 and 4.7.
  `HasSemistableReduction A O` ("some Néron model is semistable") is the **hypothesis** form, used by 3.5. With these
  choices no leaf asserts a Néron model's existence beyond what is printed; existence comes from the separate leaf
  `NeronSchemeModelExistsDVR`, with the group law obtained from the mapping property by neron-c's `grpObjOfNeron`.
* `TΩ A Ω ℓ`, `galTΩ`: `T_ℓ` and the Galois action over any algebraic closure `Ω`. By `rfl` they are the kernel's
  `A.T ℓ` and `A.galT` at `Ω = K̄`. Over `Ω`, SGA 7 IX 3.5 can be applied to `A_{K'}` with `Ω = K̄` (r8).

## 4. Proof notes and what remains

**Proved glue (no hypotheses beyond kernel leaves).**
* `dvrFiniteExtension`: a valuation ring of a finite extension `K'/K` lying over a DVR is a DVR. In the value group `G`,
  the subgroup `H = ⟨v(ϖ)⟩` has index `≤ [K':K]`, because elements in distinct cosets are linearly independent
  (`linearIndependent_of_distinct_cosets`). Then `g ↦ g^{[G:H]}` embeds `G` into the cyclic group `H`, and Mathlib's
  `valuationSubring_isDiscreteValuationRing` applies.
* `dvrComapFinite`: the restriction of a DVR of `K'` to `K` is a DVR. Its value group is a nontrivial subgroup of
  `ℤᵐ⁰ˣ`: nontrivial because the constant term of the minimal polynomial of a uniformizer would otherwise dominate.
* `isogenyBaseChangeDeg`: `φ_L` is an isogeny of the same degree. Finite and surjective follow by base change, using
  CloudW01's `overPullback_isPullback`. For `#ker`, `bcPt` and `extPt` give a bijection; the kernel points descend
  because `ker φ` is finite over `K` (`exists_ker_lift`, through the kernel's `exists_lift_of_isFinite`).
* `exists_pow_eq`, `exists_tate_lift`: `[ℓ] : A(K̄)[ℓ^{k+1}] → A(K̄)[ℓ^k]` is onto, by counting with
  `TorsionStructure`. Hence every `x ∈ A(K̄)[ℓⁿ]` is the `n`-th component of some `t ∈ T_ℓ A`. This turns the printed
  `T_ℓ` statements into the rows' finite-level forms.
* `isInertia_restrict`: inertia over `K` restricts to inertia over an intermediate `K'`.
* `exists_fixing_field`: every `K̄`-point of a `K`-scheme locally of finite type is fixed by `Aut(K̄/K'')` for some
  finite `K''`. Proof: affine open, `Spec.preimage`, finitely many generators, `IntermediateField.adjoin`.
* `exists_rational_of_fixed`: for perfect `K`, an `Aut(K̄/K)`-fixed point is `K`-rational.
* `finite_image_of_open`, `open_of_finite_image`: finite image of inertia ⟺ an open subgroup `I ∩ G_{K'}` acts
  trivially.
* `bcbcIso`, `bcbcIso_isMonHom`: `(A_{K'})_L ≅ A_L` as group schemes, from Mathlib's `Functor.mapGrpCompIso` and
  `mapGrpNatIso (Over.pullbackComp ..)`. `semistableNeronModels_transport` transports semistability along group
  isomorphisms.
* `gmTransport_height`: the kernel's model height depends only on the group scheme over `𝓞_L`. Every field of
  `MetrizedModel` except `model` is about `model.G`.

**Open glue, with what each needs.**
* `FixedTorsionRationalImperfect` (r6, imperfect `K` only). Needs: `A[m]` étale for `m` invertible (`[m]` étale,
  the bundle leaf `mulEtaleAbelianScheme` over a field), so `K̄`-points of `A[m]` are `K^sep`-points, and these are
  rational when fixed. The perfect case uses `(K̄)^{Aut} = K`, which fails for imperfect `K`.
* `SemistableLocalGlobal` (SS1-SS3). Needs:
  1. the DVRs of `L` are the `(𝓞_L)_𝔭`;
  2. Néron models localize (BLR §1.2 Prop. 4, published);
  3. the geometric special fibre of `𝒩 ⊗ (𝓞_L)_𝔭` is the fibre of `𝒩` at `𝔭`;
  4. `HasSemiAbelianIdentityComponent` is invariant under isomorphisms of the base field.
* `SemistableAlmostAll` (SS1). Needs: spreading out to an abelian scheme over `𝓞_K[1/N]` (EGA IV 8.10.5 (xii), the
  bundle leaf `egaIV_8_10_5_xii`), BLR §1.2 Prop. 8 (an abelian scheme is its own Néron model), and the observation
  that an abelian special fibre is semi-abelian with trivial torus.
* `SemistableNeronBaseChangeLocalGlobal` (SS2). Needs:
  1. the identity component of a smooth group scheme over `𝓞_L` (SGA 3 VI_B 3.10, published; Mathlib has none);
  2. the base change `𝒩 ×_{𝓞_L} 𝓞_{L'}` as a group model;
  3. the mapping-property extension `𝒩⁰_{𝓞_{L'}} → 𝒩'`;
  4. "an open immersion after every localization is an open immersion".

  SPECULATIVE: SS2 is better kept as a (c)-form leaf until identity components exist in Lean.

**Not split.**
* *Faltings' Lemma 5 in printed form.* Faltings 1983 Lemma 5 is an identity
  `h(A/G) = h(A) + ½ log deg G − [K:ℚ]^{-1} log #s^*Ω¹_{𝒢/𝓞_K}` for a finite flat subgroup scheme `𝒢`. The inequality
  in the kernel (`|h(A)-h(B)| ≤ ½ log deg φ`) also needs Raynaud's bound `#s^*Ω¹ ≤ deg G` (Astérisque 127 VII
  Cor. 2.1.3, as height-split §8 says; UNVERIFIED). Stating either needs finite flat group schemes over `𝓞_K`, their
  schematic closure, the quotient `A/G` and `s^*Ω¹`. None of these is in Mathlib or the kernel, so
  `HeightSplit.FaltingsLemma5` remains a consequence of two printed results.
* *t10.* Milne 1986 Thm 15.1 (UNVERIFIED number) is about `H¹(A_et, ℤ_ℓ) := lim H¹_et(A, ℤ/ℓⁿ)` over a separably
  closed field. The field is a statement about Mathlib's **pro-étale** `EllAdicCohomology` with a Galois action by
  transport. The split would be:
  1. (L) Milne 15.1(b) for étale cohomology;
  2. (L) the Bhatt–Scholze 2015 comparison of pro-étale and classical ℓ-adic cohomology (§5.6; UNVERIFIED);
  3. (G) naturality of both isomorphisms under the semilinear automorphisms `1 × Spec σ` of `A_K̄`. This is "canonical",
     but no source prints it.

  Mathlib 4.35 has the small étale site (`Scheme.smallEtaleTopology`) but no étale `ℤ/ℓⁿ`-cohomology package, no
  comparison, and no functoriality for these groups. The leaves cannot yet be stated against the field's objects
  without new infrastructure (several days), so t10 stays GLUE (c).

## 5. Statement review (faithfulness of the leaves and rows)

* **r6 hypothesis vs Raynaud's.** The row assumes `Aut(K̄/K)` fixes `A(K̄)[m]`; the leaf assumes the points are
  `K`-rational, the weakest theorem (strongest hypothesis). The two are equivalent for `m` invertible because `A[m]` is
  étale. Our glue is that equivalence; it is proved over perfect fields. RISK (UNVERIFIED): if SGA 7 IX 4.7 is printed
  over a strictly henselian `O`, the leaf over a general DVR is a consequence (semistability is étale-local), not the
  print.
* **SGA 7 IX 3.5.** The leaf takes the weakest reading: one `σ` at a time, `(σ-1)² = 0` on `T_ℓ`. pkg-I2 reads the
  print as "unipotent of echelon ≤ 2", and `(σ-1)(τ-1) = 0` for `σ, τ ∈ I` would imply ours.
* **SGA 7 IX 3.6.** The leaf asks for `K'` finite only (the print gives finite separable). The conclusion is at every
  place of `K'` over `O`, which is the printed scope; r8 uses the place `w ∩ K'`.
* **SGA 7 IX 3.3.** Restricted to finite `K'/K` (a specialization). The second assertion is weakened to the existence
  of an open immersion.
* **Serre–Tate Thm 2.** Printed form. "Image finite" is stated in `End_{ℤ_ℓ}(T_ℓ A)` over the kernel's `T_ℓ`.
* **BLR 1.4/3.** Scheme form, no group law, as neron-c's `NeronSchemeModelExists`, here over a DVR.
* **Rows.** All eight rows are true and no stronger than their sources: each is now proved from the sources, plus glue
  that is true (STANDARD). SS1-SS3 and faltingsLemma5BC are as height-split stated them.
* **Non-vacuity.** At the zero abelian variety, `Spec O` is a Néron model (`trivModelO_isNeronModel`), every Néron
  model is trivial (`neronO_zero_iso_unit`), and `HasSemistableReduction` and `SemistableNeronModels` hold
  (`hasSemistableReduction_zero`, `semistableNeronModels_zero`). So the hypothesis of 3.5 is satisfiable and the
  conclusions of 3.6, 3.3 and 4.7 hold there, machine-checked. The torus and abelian parts are not exercised (no
  non-zero abelian variety can be built in Mathlib 4.35). The global definitions are height-split's (§7 there).
* **Serre–Tate.** RISK (UNVERIFIED): if Thm 2 is printed for a complete (or henselian) `K`, the leaf over a general
  discrete valuation is a consequence (inertia and good reduction are insensitive to completion).

## 6. Checks

`scratch/reduct-split/chk.sh scratch/reduct-split/Reduction.lean`: about 15 s, about 7 GB, no errors. The 20
`#print axioms` lines at the end (output in `scratch/reduct-split/axioms.txt`) all report
`[propext, Classical.choice, Quot.sound]`. The run used `lean` with
`LEAN_PATH` on a symlink tree `~/rs-lib` of `~/dzq-check2/.lake/build`, which is the same commit for `ZInQKernel/`.
`TailY.olean` was compiled out of tree from the unchanged source, because the chain there had not reached it yet. To
re-check in a built worktree: `lake env lean scratch/reduct-split/Reduction.lean`.
