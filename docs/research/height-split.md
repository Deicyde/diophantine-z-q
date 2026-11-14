# height-split: the height and Faltings rows of the frontier, split into published forms

Task height-split, 2026-11-14. Base: cba8157f (fork main after w54 and frontier r3), branch
`wip/height-split`. Lean: `scratch/height-split/HeightSplit.lean` (the five Faltings-height rows,
plus H-15 as a bonus), `scratch/height-split/R5Count.lean` (H-3), `scratch/height-split/DimUnique.lean`
(development copy of a lemma merged into `HeightSplit.lean`). Results log: `scratch/height-split/log.md`.
Nothing under `ZInQKernel/` or `blueprint/` was edited. Model work; no human review.

Marks: **VERIFIED** = compiled here, or read in a named repository file; **STANDARD** = published
mathematics with a reference; **UNVERIFIED** = theorem number or display recalled without a source
(this host has no network and no copy of the papers); **SPECULATIVE** = judgement.

## 0. Main result

**All six rows are now Lean theorems.** Each one is proved from published-form leaves, the kernel's
proved glue and, for four rows, a named GLUE Prop. The rows are the kernel's own Props, imported and
never restated. Both files compile with `lake env lean`: no `sorry`, no errors, and every
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` (VERIFIED, last full runs 05:10;
§6).

**The common step: the H5 identification.** Five of the rows are about the kernel's
`stableFaltingsHeight`, an infimum in `EReal` over all number fields `L ⊇ K` and all metrized smooth
group models. The printed theorems are about Faltings' stable height: the height of the Néron
model over a field where `A` has semistable reduction. Three things are new here:
1. Lean definitions of semistable reduction (`IsSemistable`) and of the published stable height
   (`IsStableFaltingsHeight A x`).
2. Two SGA 7 IX leaves: the semistable reduction theorem and base change of the identity component.
3. A proof of the identification
   `IsStableFaltingsHeight A x ↔ stableFaltingsHeight A = x`
   (`isStableFaltingsHeight_iff`), from those two leaves, the kernel leaf N1 (Néron models exist)
   and the kernel's proved glue (H4a, H4b, M6, `NeronModelMinimal`).

As a corollary, the kernel leaf N2 (`SemistableNeronIdentityComponent`) is proved from N1 and the two
new leaves.

**A row is done when it follows from published-form leaves alone.** Two rows meet that bar:
- **H-18** (R22, Pazuki): `r22_of_upper`.
- **H-15** (R19, Gaudron–Rémond), outside the assignment: `r19_of_leaves`.

**The other rows carry named glue:**

| row | glue it still needs |
|---|---|
| H-14 | `NeronMetrizable` |
| H-17 | the kernel's `AnalyticUniformizationUnique` |
| H-19 | `NeronMetrizable` and `AnalyticUniformizationUnique` |
| H-16 | `IsogenySemistableBaseChange` |
| H-3 | `QMPairEmbeddingCorrespondence` |

The glue Prop `MetrizedDimUnique` (two metrizations of one model have the same `g`) was introduced
and then **proved** with a 2-torsion count (`metrizedDimUnique`).

**Verdicts on the statements.** No row is false or vacuous.
- Every row's literature content is no stronger than its source.
- Two rows also contain a finiteness clause about the project's definition, which no printed theorem
  supplies:
  - H-17 (R21) implies `stableFaltingsHeight A ≠ ⊥`;
  - H-14 (R18) implies `stableFaltingsHeight A ≠ ⊤`.

  Those clauses are exactly the two halves of H-19, and the proofs route them through H-19's glue.
- H-18 (R22) is weaker than Pazuki's printed corollary in four respects. It is not stronger, so its
  "hardened" label does not mean "stronger than printed" (§3).

### The table

Lean names are in namespace `ZInQ.HeightSplit`; for H-3, `ZInQ.HeightSplit.R5`.
- **Leaves:** N1 = kernel `ZInQ.H5Neron.NeronModelExists` (BLR 1.4/3); SS1 = `SemistableReductionThm`;
  SS2 = `SemistableNeronBaseChange`.
- **"Id.":** the identification `isStableFaltingsHeight_iff`, which is proved from N1, SS1 and SS2.
- **AN3U:** the kernel's `ZInQ.DefFaltings.AnalyticUniformizationUnique` (open, complex analysis).

| row | old form (frontier r3) | new leaves (published form, source) | new glue | Lean name of the proof |
|---|---|---|---|---|
| H-14 `r18` | `R18_Javanpeykar`: `h_F^st(J) ≤ 13·10⁶ g d⁵` over the kernel's infimum; GLUE (consequence) | `JavanpeykarBound` (Javanpeykar, ANT 8 (2014) Thm 1.1.1, specialized to curves over `K` with a `K`-rational Belyi function, over `IsStableFaltingsHeight`); N1, SS1, SS2 | `NeronMetrizable` (the `≠ ⊤` half) | `r18_of_leaves` |
| H-16 `r20` | `R20_FaltingsLemma5`: `\|x − y\| ≤ ½ log deg φ` for real kernel heights; GLUE (consequence) | `FaltingsLemma5` (Faltings 1983 Lemma 5 / Raynaud Ast. 127 VII 2.1.3, semistable form over `𝓞_K`; UNVERIFIED, unread); N1, SS1, SS2 | `IsogenySemistableBaseChange` | `r20_of_leaves` |
| H-17 `r21` | `R21_Bost`: `−(3/2) g ≤ h_F^st(A)` in `EReal`; GLUE (via Gaudron–Rémond §9) | `BostLowerBound` (Bost, Sém. Bourbaki 795: `h_D ≥ −(g/2) log 2π`, Deligne normalization, display UNVERIFIED); GR's printed form `GRBostBound` is derived (`grBostBound_of_bost`); N1, SS1, SS2 | AN3U (the `≠ ⊥` half); `MetrizedDimUnique` introduced and **proved** | `r21_of_leaves'` (`r21_of_leaves` with `MetrizedDimUnique` as a hypothesis) |
| H-18 `r22` | `R22_Pazuki`: `h(z) ≤ X/2 + C₂ log(X+2)`, `X ≥ max(1, h_F + log π)`; GLUE ("hardened") | `PazukiCor13Upper` (upper half of Pazuki, Bull. SMF 140 (2012) Cor. 1.3(2), `ℓ²` theta height, Deligne's `h_D`); the two-sided `PazukiCor13` implies it; N1, SS1, SS2 | none | `r22_of_upper` (`r22_of_leaves` from the two-sided form) |
| H-19 `h5fin` | `StableHeightFinite`: `h_F^st(A) ∉ {⊤, ⊥}`; GLUE (theorem + definition) | N1, SS1 (SGA 7 IX 3.6), SS2 (SGA 7 IX 3.3) | `NeronMetrizable`; AN3U; `MetrizedDimUnique` **proved** | `stableHeightFinite_of'` (`stableHeightFinite_of` with `MetrizedDimUnique` as a hypothesis) |
| H-3 `r5count` | `R5fpCount`: `#{QM classes over ℚ̄ with End_𝒪 ≅ R} = 2^{b(k)} h(R)`; GLUE (consequence of González–Rotger Prop. 5.6) | `EichlerOptimalEmbeddingCount` (Eichler 1955; Vignéras LNM 800 III 5.11–5.12; numbers UNVERIFIED): optimal embeddings `R ↪ 𝒪` modulo `𝒪^×` are finite, `= h(R)∏_{p∣6}(1 − (k/p))` | `QMPairEmbeddingCorrespondence` (Shimura uniformization: an `Equiv` between the QM classes and the embedding classes) | `R5.r5fpCount_of` |
| H-15 `r19` (bonus) | `R19_GaudronRemond` over the kernel height; LEAF | `GaudronRemondThm14` (GR Duke 163 (2014) Thm 1.4 over `IsStableFaltingsHeight`); N1, SS1, SS2 | none | `r19_of_leaves` |

## 1. The published stable height in Lean (`HeightSplit.lean` §A-§B)

**Semistable reduction.** `HasSemiAbelianIdentityComponent G`, for a group scheme `G` over a field
`k`, holds when all of the following exist:
- an open immersion of group schemes `U → G` with `U` connected (so `U = G⁰`);
- an abelian variety `B` over `k` (the kernel's `PkgI3.AbVar`);
- a flat, surjective homomorphism `π : U → B`;
- for some `r`, an identification of `ker(U(R) → B(R))` with `(Rˣ)^r`, as groups and naturally in
  every `k`-algebra `R`.

By Yoneda the last item says `ker π ≅ 𝔾_m^r`, so `G⁰` is an extension of an abelian variety by a
split torus (SGA 7 IX 2.2/3.1, BLR 7.4, UNVERIFIED locators).

`IsSemistable 𝒩` requires this, at every maximal ideal `𝔭` of `𝓞_L`, for the geometric fibre
`𝒩 ×_{𝓞_L} κ̄(𝔭)`. Here `κ̄(𝔭) = AlgebraicClosure 𝔭.ResidueField`, and the group structure on the
fibre comes from the monoidal functor `Over.pullback`.

**The published height.** `IsStableFaltingsHeight A x` holds when, for some number field `L ⊇ K`,
some Néron model `𝒩` of `A_L` (the kernel's `IsNeronModel`) satisfies `IsSemistable 𝒩` and
`𝒩.height = x`. `𝒩.height` is the kernel's height of a group model: the metrized Hodge line
`⋀^g ω_𝒩` with Faltings' normalization `(i/2)^g`. This is Faltings' definition of the stable height
(Faltings 1983 §1; Deligne, Sém. Bourbaki 616; UNVERIFIED locators).

**The two SGA 7 IX leaves.**
- **SS1** `SemistableReductionThm`: for every `A` over a number field there is a finite `L₀` such that
  every Néron model of `A_{L₀}` is semistable.
  - This is SGA 7 IX Thm 3.6 in global form.
  - SGA 7 states it over a discrete valuation ring. The global form follows from good reduction
    outside finitely many primes and from the persistence of semistability, as the definition of
    the stable height uses it.
  - Strictly it is a consequence of one theorem, not its literal form.
- **SS2** `SemistableNeronBaseChange`: if `𝒩` is a semistable Néron model of `A_L` and `L'/L` is finite,
  then the identity component of the Néron model of `A_{L'}` is the base change of `𝒩⁰`.
  - This is SGA 7 IX 3.3.
  - It is stated with the kernel's `IsBaseChangeOf` and `IsOpenSubgroupModel`, exactly in the form of
    the kernel's N2 clause.
  - The identity component as an open subgroup is SGA 3 VI_B 3.10.
  - Also a consequence-level form.

**Proved from N1 and SS2** (VERIFIED):
- `stableFaltingsHeight_eq_of_semistable`: the kernel's height equals `𝒩₀.height` for every
  semistable Néron model `𝒩₀`. The argument is that of `H5Neron.stableFaltingsHeight_eq_neron_all`,
  with H4a, M6 and `NeronModelMinimal` from `ZInQ.Contrib.HeightBC`.
- `isStableFaltingsHeight_unique`: the published definition does not depend on the field.

**Proved from N1, SS1 and SS2** (VERIFIED):
- `isStableFaltingsHeight_iff`;
- `exists_semistable_neron`;
- `semistableNeronIdentityComponent_of`, the kernel leaf N2.

## 2. H-17 (R21): how the row differs from the printed statement

**The row**, `ZInQ.DefFaltings.R21_Bost`: for every `A` over a number field with `A.dim = g`,
`((−(3/2) g : ℝ) : EReal) ≤ stableFaltingsHeight A`.

**The printed statements.**
- **(i) Bost**, Sém. Bourbaki 795 (Astérisque 237): `h(A) ≥ −(g/2) log(2π)` for the stable height in
  Deligne's normalization. The display is UNVERIFIED: locators.md could not read it.
- **(ii) Gaudron–Rémond 2014**, §9, proof of Lemma 9.1, p. 2098: GR use `h_F(A) ≥ −(3/2) dim A`
  (Faltings' normalization) and refer it to Bost and to their earlier Cor. 8.4. The audit read this.
  It is an inequality inside a proof, not a numbered statement.

**Differences between the row and (i):**
1. **Height object.** The row uses the kernel's infimum in `EReal`; Bost uses the published height, a
   real number. The bridge is `isStableFaltingsHeight_iff` (N1, SS1, SS2).
2. **Finiteness.** For an abelian variety `dim A` is finite, so the row asserts
   `stableFaltingsHeight A ≠ ⊥` for every `A`. No printed theorem says this, because the printed
   height is real by definition. It is a statement about the project's definition: half of H-19.
   Here it is proved from AN3U (open), `MetrizedDimUnique` (now proved) and N1, SS1, SS2
   (`stableFaltingsHeight_ne_bot`).
3. **Constant.** `−(3/2) g` is weaker than Bost's bound converted to Faltings' normalization,
   `h_F = h_D − (g/2) log π ≥ −(g/2) log(2π²) ≈ −1.4915 g`. The step is
   `log(2π) + log π < 3`, i.e. `2π² < 19.9 < e³`, proved as `log_two_pi_add_log_pi_lt_three` and
   `grBostBound_of_bost`.
4. **Normalization.** The row is in Faltings' normalization `(i/2)^g`, Bost in Deligne's. The leaf is
   stated in Deligne's form, `x + (g/2) log π ≥ −(g/2) log(2π)`, which is the weaker of the two
   readings.
   - A display in Faltings' normalization would imply it, since `h_D ≥ h_F`.
   - The Faltings-normalized reading is in any case false: for `E` with `j = 0`,
     `h_F ≈ −0.749 − ½ log π ≈ −1.32 < −½ log 2π`. Deligne's normalization is therefore the one
     Bost means. This is STANDARD (Deligne's value for `j = 0`), recalled from memory, so UNVERIFIED.

**Verdict.** The row is not stronger than Bost's printed bound, apart from the finiteness clause 2,
which is now isolated as glue.
- **Printed form:** `BostLowerBound`.
- **The extra argument:** the arithmetic of item 3, proved, and the identification, proved from
  leaves.
- **Glue:** AN3U, for `≠ ⊥`.

## 3. H-18 (R22): how the row differs from the printed statement

**The row**, `ZInQ.LeafPush2.R22_Pazuki`, has these hypotheses:
- an abelian surface `A/K` with `stableFaltingsHeight A = x` (real);
- `X ≥ max(1, x + log π)`;
- for some `σ : K → ℂ`, an analytic uniformization `(Λ, Φ)` of `A(ℂ)_σ`;
- a Siegel `Ω` that is a period matrix of `Λ`;
- an algebraic representative `z ∈ F^16` with `emb(z_m) = c·θ[m](0, Ω)`.

It concludes `absLogHeight z ≤ X/2 + C₂ log(X + 2)`, where `absLogHeight` is Mathlib's sup-norm
Weil height divided by the degree.

**The printed statement** (Pazuki 2012, Cor. 1.3(2), `g = r = 2`, read by the audit): for a principally
polarized abelian surface `(A, L)` over `ℚ̄`,
`|max(1, h_Θ) − max(1, h_D)/2| ≤ C₂ log(min(max(1, h_Θ), max(1, h_D)) + 2)`. Here `h_D` is the stable
height in Deligne's metric, `h_Θ` is the theta height with `ℓ²` (Fubini–Study) norms at the infinite
places, and `C₂ = 1000·2⁴(log 2⁴)⁵`.

**The row is weaker than the printed statement in four respects:**
1. it keeps only the upper side of the absolute value;
2. it replaces the minimum inside the logarithm by `X ≥ max(1, h_D)`;
3. it uses the sup-norm height, which is at most the `ℓ²` height (`absLogHeight_le_absLogHeightL2`,
   proved: `max_i |z_i|_v ≤ (∑_i |z_i|_v²)^{1/2}` at each archimedean place);
4. it uses `h(z) ≤ max(1, h_Θ)`.

**It differs from the printed statement in the following readings, none of which makes it
stronger:**
- **Height.** The row uses the kernel's height plus `log π`. With `h_D = h_F + (g/2) log π` (Deligne's
  metric) the two agree through `isStableFaltingsHeight_iff`.
- **Base field.** `A` is defined over a number field. This is a specialization; heights are invariant
  under extension of the base field.
- **Polarization.** The polarization is given analytically, by a Siegel period matrix of `Λ`.
  - Every such `Ω` gives the principal polarization `(Im Ω)⁻¹` with a symplectic basis.
  - Every analytic polarization of `A(ℂ)_σ` is algebraic and defined over `ℚ̄` (Riemann/Lefschetz;
    STANDARD, not formalized).
- **Theta coordinates.** The row uses the classical `θ[a;b](0, Ω)`, `a, b ∈ {0, ½}²`, as Pazuki's
  level-2 coordinates. This identification is UNVERIFIED (Def. 2.6 unread; leaf-review-b premise 3).
  A change of symplectic basis permutes the coordinates up to roots of unity and a common factor, so
  the height does not depend on it.

**Verdict.** The row is not stronger than the printed corollary.

"Hardened" in the frontier refers to the bookkeeping form `R22_plus3` (`X = max(1, h_F + 3)`, which
covers any normalization shift up to 3). That form is a theorem derived from the row. The row itself
is the `log π` form.

**What is proved:**
- **Printed form:** `PazukiCor13`, two-sided. The row needs only its upper side, `PazukiCor13Upper`
  (read off the same display; `pazukiCor13Upper_of`).
- **The extra argument**, all proved:
  - `pazuki_upper_of_upper` (items 1, 2, 4);
  - `absLogHeight_le_absLogHeightL2` (item 3);
  - the identification.

  There is no glue.

## 4. The other rows

**H-14 (R18, Javanpeykar).**
- **Leaf** `JavanpeykarBound`: the row's statement with `stableFaltingsHeight J ≤ B` replaced by
  `∀ x, IsStableFaltingsHeight J x → x ≤ B`.
- **Reading.** This is a specialization of the printed theorem, which is stated over `ℚ̄`. A curve
  over `K` with a `K`-rational Belyi function of degree `d` has `deg_B(X_ℚ̄) ≤ d`. The bound is stated
  in Faltings' normalization, the weaker reading if the paper used Deligne's.
- **Extra content.** The row also asserts `stableFaltingsHeight J ≠ ⊤`. That is the `≠ ⊤` half of
  H-19, supplied by the glue `NeronMetrizable`.

**H-16 (R20, Faltings' Lemma 5).**
- **Leaf** `FaltingsLemma5`, in the semistable form: `A`, `B` over `K` with semistable Néron models
  over `𝓞_K` and an isogeny `φ` over `K` give `|h(𝒩_A) − h(𝒩_B)| ≤ ½ log deg φ`.
- **Source status.** Faltings' Lemma 5 is UNVERIFIED (unread). The inequality is the form Pazuki 2012,
  Remark 2.3, attributes to it.
- **Glue** `IsogenySemistableBaseChange`: it moves an isogeny over `K` with published heights `x`, `y`
  to an isogeny of the same degree over a field `L` where both sides are semistable, with Néron-model
  heights `x`, `y`. It needs four things:
  - base change of isogenies, and invariance of `#ker(K̄)`;
  - SGA 7 IX 3.3 for persistence of semistability;
  - transport of group models along `(A_L)_L ≅ A_L`;
  - `isStableFaltingsHeight_unique`.

**H-19 (`StableHeightFinite`).** The `≠ ⊤` half is `stableFaltingsHeight_ne_top`, from N1 and
`NeronMetrizable`. The `≠ ⊥` half is `stableFaltingsHeight_ne_bot`, from N1, SS1, SS2, AN3U and
`MetrizedDimUnique` (proved).

**H-3 (R5fpCount).** `R5.r5fpCount_of` derives the row from two inputs.
- **Leaf** `EichlerOptimalEmbeddingCount`, for `B = (2, −3)_ℚ` (the kernel's `LeafQM.B`) and the
  maximal order `𝒪` (`LeafQM.O`):
  - the `𝒪^×`-conjugacy classes of `ℚ`-algebra maps `φ : k → B` with `φ⁻¹(𝒪) = R` are finite;
  - their number is `eichlerFactor k 2 · eichlerFactor k 3 · #Pic(R)`, where the factor is 2 if
    `p𝓞_k` is prime, 1 if it is the square of a prime, and 0 otherwise.
- **Glue** `QMPairEmbeddingCorrespondence`: an `Equiv` between the row's set of QM classes and the
  embedding classes.

The derivation: a QM pair exists, so the embedding classes are nonempty. They are finite, so their
number is positive, no factor vanishes, and each factor is `2^{[p inert]}`, which gives
`2^{inertCount6 k}`.

Caveat on the leaf: some sources count modulo `𝒪¹`, which gives an extra factor 2. Which form is
printed is UNVERIFIED; the `𝒪^×` form is the one that matches the hand checks of leaf-review-a §5.6
(`ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`: 2; discriminant `−19`: 4).

## 5. The glue that remains, and what each Prop needs

| glue | rows | what it needs |
|---|---|---|
| `NeronMetrizable` | H-14, H-19 | the kernel's `AnalyticUniformizationExists` (Mumford AV §1); `HodgeLatticeTheorem` (proved in `ZInQ.Contrib.Dim`); dimension of the uniformization = `dim A`; construction of the coefficient map from the differential at `0` of germs along `Φ` (well defined on `𝔪/𝔪²`, nonzero on the Hodge line) |
| `AnalyticUniformizationUnique` (kernel) | H-17, H-19 | a holomorphic homomorphism of complex tori lifts to a linear map; needs local coordinates on `𝒢(ℂ)_τ` from regular functions (smoothness, Jacobian criterion) |
| `IsogenySemistableBaseChange` | H-16 | see §4 |
| `QMPairEmbeddingCorrespondence` | H-3 | Shimura's uniformization of QM abelian surfaces (`H₁` free of rank one over `𝒪`, class number one); CM points are fixed points of `φ(k^×)` with `End_𝒪 ≅ φ(k) ∩ 𝒪`; descent from `ℂ` to `ℚ̄`; algebraicity of QM tori |
| ~~`MetrizedDimUnique`~~ | H-17, H-19 | **proved** (`metrizedDimUnique`): `#𝒢(ℂ)_τ[2] = #(Λ/2Λ) = 2^{2g}`, via `AddSubgroup.index_range_nsmul` and `ZLattice.rank` |

## 6. What compiles

All checks used `lake env lean`, one process at a time (VERIFIED).
- **`scratch/height-split/HeightSplit.lean`.** It imports `ZInQKernel.HDecomp.LeafPush2.R22` and
  `ZInQKernel.Contrib.HeightBC.Main`. Exit 0, no errors or warnings, about 10 s. All 16
  `#print axioms` lines are standard.
- **`scratch/height-split/R5Count.lean`.** It imports `ZInQKernel.HDecomp.QM.Leaves`. Exit 0, about
  6 s. `#print axioms R5.r5fpCount_of` is standard.
- **`scratch/height-split/DimUnique.lean`.** It imports `ZInQKernel.HDecomp.Faltings.Height`. Exit 0,
  and its axioms are standard.

## 7. Caveats

- **Locators.** Every locator above that was not read by docs/research/locators.md is UNVERIFIED.
  That covers SGA 7 IX 3.3 and 3.6, Bost's display, Faltings' Lemma 5, Eichler/Vignéras numbering
  and Pazuki's Def. 2.6 coordinates.
- **Leaf forms.** SS1, SS2 and `JavanpeykarBound` are stated in the forms the definitions need: global
  form, open-subgroup form, and over `K`. Each is a consequence of one printed theorem by the standard
  steps named in its docstring. A reader applying the strict classification may count them as
  consequences rather than literal forms.
- **Non-vacuity of the new definitions** (`IsSemistable`, `IsStableFaltingsHeight`) is not
  machine-checked; Mathlib cannot construct a nonzero abelian variety. They were written to match the
  printed definitions.
