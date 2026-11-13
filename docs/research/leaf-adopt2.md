# leaf-adopt2: leaf-push2 and rv-qm-polar folded into the H decomposition

Status: research note (task leaf-adopt2, 2026-11-12). It continues docs/research/leaf-adopt.md.

Files:
- Edited: `scratch/h-decomposition/Leaves.lean` and `docs/research/h-decomposition.md`.
- New: `scratch/leaf-adopt2/fold.py`, the one-shot insertion script. Re-running it on the base
  commit 01267822 reproduces `Leaves.lean` byte for byte (VERIFIED).
- New: `scratch/leaf-adopt2/docs_edit.py`, the edits to the note.
- New: the results log `scratch/leaf-adopt2/log.md` and the compiler outputs
  `scratch/leaf-adopt2/compile{2,3}.txt`.

No file under `ZInQKernel/`, `blueprint/` or another task's directory was edited.

Marks:
- **VERIFIED**: compiled, counted or read here.
- **STANDARD**: published, with a reference.
- **SPECULATIVE**: an assessment.
- **UNVERIFIED**: a theorem number recalled from memory. There is no network access.

## 0. Main result

**`Leaves.lean` now states 53 of the 56 leaves of the H decomposition concretely, plus three of
the four parts of R1.** Only R17, T10 and R1(b) remain `opaque` placeholders. Before this task
there were 48 concrete leaves and 7 placeholders plus R1(b).

VERIFIED: `lake env lean scratch/h-decomposition/Leaves.lean` exits 0 in 194 s (21 705 lines).
- One `sorry`, unchanged: `HSyn.glueOutputs_of_leaves`.
- 3 `opaque`, no `axiom`.
- 131 `#print axioms` lines. All give `propext`, `Classical.choice`, `Quot.sound`, except the two
  lines for `HSyn.sixContactMin_of_leaves`, which add `sorryAx` through that `sorry`.

What changed:
- **R3, R18, R22.** They are now leaf-push2's statements: `ZInQ.LeafPush2.R03_LinYang`,
  `R18_Javanpeykar`, `R22_Pazuki`.
- **T11** is now two concrete textbook leaves, `T11a_RiemannEnd` and `T11b_Rigidity`.
- **T12 is glue.** The form G10 uses, `T12_ComplexConjEigen`, is a glue target from T35, T5 and
  T26 (unproved).
- **New textbook leaf T35** = `ZInQ.LeafPush2.UniformizationExists`: AN3 for abelian varieties,
  Mumford §1 with GAGA. I kept it rather than bp-analytic's `UniformizationLeaf` (§2).
- **rv-qm-polar is applied.** Every docstring of a QM leaf now cites **Lemma P** with its
  conditions (type `μ` fixed, characteristic 0, `𝒪` maximal) instead of the SPECULATIVE
  bp-qmmoduli §2.2. No statement changed: rv-qm-polar §2 found none that needs correcting.

Every statement-bearing line of the folded leaves is identical to its source (difflib, §1).

**Own check of the diff (§5).** Each replaced leaf is the published statement or a consequence of
it, never stronger, and not vacuous because of a definitional mistake. My reading and one
independent read-only model review agree: **no DEFECT**. Two RISKs remain, both already disclosed
in the docstrings:
- R22: Pazuki's level-2 coordinates are identified with the classical `θ[a;b](0, Ω)`
  (UNVERIFIED).
- R3: the `J` convention is checked only against hdec-elementary's transcription.

One unstated premise was found and recorded: R22 needs **both** halves of H5, for leaf-push2's
copy of the height. This is the new glue target `HSyn.HeightCopiesAgree`.

| Leaf | Before | Now (Lean name) | Source |
| --- | --- | --- | --- |
| R3 | placeholder | `ZInQ.LeafPush2.R03_LinYang` (over `ℂ`, existential, polarization-free) | leaf-push2 |
| R18 | placeholder | `ZInQ.LeafPush2.R18_Javanpeykar` (`g := dim J`, `EReal`) | leaf-push2 |
| R22 | placeholder | `ZInQ.LeafPush2.R22_Pazuki` (all uniformizations, all period matrices) | leaf-push2 |
| T11 | placeholder | `ZInQ.LeafPush2.T11a_RiemannEnd`, `T11b_Rigidity` | leaf-push2 |
| T12 | placeholder | **glue**: target `ZInQ.LeafPush2.T12_ComplexConjEigen` (unproved) | leaf-push2 |
| T35 (new) | — | `ZInQ.LeafPush2.UniformizationExists` | leaf-push2 (kept over bp-analytic, §2) |

**Counts.** VERIFIED: the bundle fields were counted with a regex over the compiled file.
- Research-level leaves (23):
  - concrete: R2-R16, R18-R22, H5 (**21**), plus R1 in part;
  - placeholders: R17 and R1(b).
- Textbook leaves (33):
  - concrete: T1-T11, T13-T31, T33-T35 (**32**);
  - placeholder: T10.
- Bundle fields:
  - `ResearchLeaves` has 26 fields, 24 of them concrete (`opaque`: `r1an`, `r17`);
  - `TextbookLeaves` has 38 fields, 37 of them concrete (`opaque`: `t10`);
  - in all, **61 concrete Props and 3 placeholders**.

## 1. How the file was folded (VERIFIED)

`scratch/leaf-push2/LeafPush2.lean` imports `ZInQKernel.HDecomp.Objects`. That module defines
`PkgI3`, which `Leaves.lean` also defines, so the file cannot be imported. Its body, from the
module docstring to `end ZInQ.LeafPush2`, without the imports and the `#print axioms` lines, is
copied as a new section `LeafPush2Sec` placed after `LeafAdoptSec`. Its own `#print axioms` lines
are appended at the end of the file.

The names it uses from the kernel resolve to `Leaves.lean`'s copies of the kernel definitions,
which leaf-adopt checked to be identical: `PkgI3.AbVar`, `.baseChange`, `.dim`, `.End`, `.galRep`,
`.T`.

difflib of the copied section against its source shows these changes:

| Change | Why |
| --- | --- |
| a header paragraph in the module docstring | records the provenance |
| R3 docstring, premise bullet: "bp-qmmoduli §2.2 … SPECULATIVE, under review in rv-qm-polar" ↦ Lemma P with its conditions and status | rv-qm-polar §4 |
| R3 docstring, polarization paragraph: "if a QM surface carries several principal polarizations" ↦ "although it carries several (one per type `c`, `c² = −6`); only the type-`μ` one is used" | rv-qm-polar §1.3 shows that there are several |
| the two `_root_` declarations `PeriodPair.lattice1` and `PeriodPair.covolume_lattice1` replaced by comments | they are already in `DefFaltingsSec`, with identical text (diff of the two 17-line blocks is empty); a second declaration is an error (first compile: 2 errors, exactly these) |

No other line differs. Elsewhere in `Leaves.lean`:
- **Placeholders.** The five `opaque` placeholders R3, R18, R22, T11 and T12 are replaced by
  comment blocks naming their successors.
- **Bundles.** Fields `r3`, `r18`, `r22`, `t11a`, `t11b`, `t35`; `t11` and `t12` are removed.
- **Glue, one new proof.** `HSyn.isComplexConj_leafPush2_iff`: leaf-push2's `IsComplexConj` is
  `PkgI4.IsComplexConj` (`Iff.rfl`, standard axioms).
- **Glue, one new target.** `HSyn.HeightCopiesAgree` (a `def … : Prop`; unproved; §4).
- **File header.**

## 2. `UniformizationExists` against bp-analytic's `UniformizationLeaf`: keep `UniformizationExists`

| | leaf-push2 `UniformizationExists` (kept, T35) | bp-analytic `UniformizationLeaf` |
| --- | --- | --- |
| field | every `K` with `σ : K → ℂ`; points `CPts A σ = Hom_K(Spec ℂ, A)` | `K = ℂ`, `σ = id` |
| dimension | `g` with `A.dim = g` (Krull dimension) | `g` existential |
| map | `Φ : ℂ^g → A(ℂ)_σ`: a surjective homomorphism with kernel `Λ` (a full lattice) | `φ : ℂ^g/Λ ≃+ A(ℂ)` |
| analytic clauses | Zariski preimages open; regular functions `DifferentiableOn` on them | (i) the same with `AnalyticOnNhd`; (ii) local holomorphic coordinates; (iii) `φ⁻¹` continuous |
| glue proved over it | none needed by R22 or T11a; torsion `A(ℂ)[n] = Φ(n⁻¹Λ)` is pure algebra | uniqueness up to `ℂ`-linear maps, the analytic representation, torsion (Mathlib-only file) |

Reasons for keeping `UniformizationExists` (VERIFIED by reading both files):
1. **Its predicate is the one the consumers quantify over.** R22 and T11a take
   `ZInQ.LeafPush2.IsUniformization` as a hypothesis, so leaf and consumers share one definition
   and need no conversion glue. With `UniformizationLeaf`, a bridge would be needed first.
2. **It ties `g` to `dim A`.** R22 (`A.dim = 2`, `Φ` on `Fin 2 → ℂ`), T11a (`A.dim = g`) and T12
   (eigenspaces of dimension `dim A`) need this. bp-analytic's `g` is existential. Its clause (ii)
   forces `g` to be the analytic dimension, but relating that to `topologicalKrullDim` is glue
   that nobody has written.
3. **It covers every `K` with `σ`.** R22 needs `A` over a number field at each complex place.
   bp-analytic would need base change along `σ` first.

The cost of this choice:
- bp-analytic's predicate is stronger: with (ii) and (iii), uniqueness and the analytic
  representation are theorems. Over leaf-push2's weaker predicate, the analytic representation is
  the leaf T11a instead of glue.
- A weaker predicate in the *hypothesis* of R22 and T11a makes those leaves assert more. They stay
  consequences, because with `g = dim A` the weak predicate already forces `Φ = π ∘ L` with `L` a
  `ℂ`-linear isomorphism. The argument: `Φ` is a continuous holomorphic surjective homomorphism of
  complex Lie groups of equal dimension, so it lifts linearly. This is my reading and the
  independent review's (STANDARD). An `ℝ`-linear `T` in `IsPeriodMatrix` would have been a defect;
  it is `ℂ`-linear.
- bp-analytic's file stays the blueprint for *proving* T35 (complex tori, the exponential, period
  lattices) and for the T12 glue (torsion, conjugation).

Two bridges, not built:
- `IsUniformization` of bp-analytic with `g = dim A` implies leaf-push2's for `Φ := φ ∘ proj`.
  This is easy: homomorphism, kernel and surjectivity from `φ` being an isomorphism; openness and
  holomorphy from (i).
- If uniqueness glue is ever needed, (ii) and (iii) can be added to T35 as conjuncts. They are
  consequences of Mumford §1 too.

## 3. rv-qm-polar applied (docstrings only)

Lemma P, as used in every docstring:

> For a fixed `μ` (N5's `2j+ij`), the type-`μ` principal polarization of `(A, ι)` exists and is
> unique in characteristic 0, also at CM points.

Its conditions are C1 (type fixed), C2 (characteristic 0) and C3 (`𝒪` maximal). Its status:
- VERIFIED as an argument (rv-qm-polar §1.2);
- lattice cores compiled: `eq_pm_E0_of_principal`, `type_eq_mu_mul`; sign step `lemmaP_lattice`;
- class number one and the descent from `ℂ` are not in Lean;
- published locators (Buzzard 1997 p. 592; Rotger 2003, 2004) UNVERIFIED; if they print only
  uniqueness, existence becomes glue.

It is folded into each leaf because polarizations cannot be stated in Lean yet.

Where it now replaces "bp-qmmoduli §2.2 … SPECULATIVE":
- in `Leaves.lean`, the docstrings of `LeafQM.AV.QML3`, `R1fp` (two places), `R5fp`,
  `R5fpCount`, `QMLeaves`, `LeafAdopt.R1R2fpRep`, `R5fpStrong`, the R1 comment, R1(b), the bundle
  fields `r1r2`, `r1rec`, `r5`, `r5count`, `r3`, the R3 docstring and the file header;
- in h-decomposition.md:
  - §2.1: the premise paragraphs of R1, R2 and R5 (three identical paragraphs) and the new R3
    paragraph;
  - §0, §2.3, §4, §5 (WP12) and §6 R7.

What stays SPECULATIVE, as rv-qm-polar says:
- the polarized form of A7 (written, not compiled at the abelian-variety level);
- the bijection of §1.3, for which no source was read;
- `π₀(A) = 1` for `D = 6` (evidence only) and the Eichler count.

No leaf uses any of these. Lemma P's conditions hold for every QM leaf:
- R1, R2, R5 are over fields of characteristic 0;
- R3 is over `ℂ`;
- `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` is maximal (reduced discriminant 6, confirmed by the review).

The historical records were not rewritten; they are marked "now Lemma P" where they state counts:
- leaf-adopt's changelog in h-decomposition §0;
- the superseded count bullets.

bp-qmmoduli.md itself belongs to another task and was not edited; rv-qm-polar §4 item 1 gives its
repair text.

## 4. Glue impact

- **No glue step consumed a removed placeholder.** They occurred only in the bundles, and
  `glueOutputs_of_leaves` ignores its arguments. So no glue statement changed.
- **Proved glue now in `Leaves.lean`**, from leaf-push2:
  - `R22_plus3`: the hardened form `X = max(1, h + 3)` that G19 uses;
  - `R18_real`;
  - `linYangTuple_onQMLocus`, `onQMLocus_of_linYangTuple`: Lin–Yang's tuple is hdec-elementary's
    `OnQMLocus`;
  - `linYang_j_eq`: F1's `j = 3779136·I₁₀²/I₄⁵`;
  - `R03_of_algClosed`, `exists_isComplexConj`, `isSiegel_I`, `javanpeykarBound_pos`, `_mono`.
- **Proved glue from this task:** `HSyn.isComplexConj_leafPush2_iff`.
- **Glue targets** (unproved, not leaves):
  - `T12_ComplexConjEigen`, from T35, T5, T26 and the antiholomorphy of conjugation;
  - `R03_LinYang_algClosed`, the Lefschetz principle, which gives the `ℚ̄`-form used at A7 and F1;
  - `HSyn.HeightCopiesAgree`, new. R18 and R22 are over leaf-push2's copy of the stable height
    (on `PkgI3.AbVar`), while R19-R21 and H5 are over def-faltings' copy. The two are textual
    copies, so the identification along `LeafAdopt.abVarEquiv` is pure transport. It is long,
    because every structure of the Arakelov layer is duplicated (`HermitianLattice`, `HodgeData`,
    `GroupModel`, `MetrizedModel`). It is what lets the glue apply the bundle's H5 to R18 and
    R22.

## 5. Own check of the diff

**Method.**
- I read every replaced leaf and the definitions it uses: `IsBelyiFunction`, `ffAlgebra`,
  `IsJacobian`, `IsUniformization`, `cEvalAt`, `IsSiegel`, `IsPeriodMatrix`, `thetaConst`,
  `absLogHeight`, `QMStr`, `IC*`, `IgJ*`, `LinYangTuple`, `HasSexticModel`, `AbVar.baseChange`.
- I checked the stated forms against the sources as recorded in locators.md and leaf-push2 §3.
- Independent check: one read-only model review (a subagent; no Lean process; given the code and
  the background notes, not my conclusions). Its findings agree with mine. Points it added are
  marked *(review)*.
- This is a model check, not a human one.

| Leaf | (a) published or consequence, never stronger | (b) non-vacuous | (c) premises | verdict |
| --- | --- | --- | --- | --- |
| `R18_Javanpeykar` | consequence, note 1 | yes: hypotheses satisfiable for a Jacobian with a Belyi function; `0 < d` excludes the junk `finrank = 0` | H5's upper half, for leaf-push2's copy of the height: if no `MetrizedModel` existed, `h = ⊤` and the leaf would be **false**, not vacuous *(review)*; normalization (Faltings or Deligne; a normalization without `2^{-g}` would make it stronger, low risk) | OK (premise disclosed) |
| `R22_Pazuki` | consequence, note 2 | yes: `𝔥₂ ≠ ∅` (`isSiegel_I`); the even theta constants are not all 0, so the tuple is nonzero *(review)*; needs T35 and algebraicity of the theta-null point | H5, **both halves**: the height enters as a hypothesis `= x`, so an infimum below the published `h_F` would make the leaf stronger *(review; now in h-decomposition R22)*; algebraicity of analytic polarizations (T11-type); Pazuki's Def. 2.6 = classical `θ[a;b](0, Ω)` (UNVERIFIED) | RISK |
| `R03_LinYang` | consequence, note 3 | yes: `dim A = 2` with `𝒪 ↪ End A` excludes `A = 0` | Lemma P (conditions hold over `ℂ`); Weil's dichotomy at `j ∈ {0, ∞}` (UNVERIFIED locator); the tuple is checked against hdec-elementary's `OnQMLocus`, not against the printed (13)-(14) | RISK (low) |
| `UniformizationExists` (T35) | Mumford §1 with GAGA for `A ×_{K,σ} ℂ`; every clause holds for the exponential; `g = 0` is fine (`ℂ⁰`, `Λ = 0`, one point) | yes | none | OK |
| `T11a_RiemannEnd` | part 1: `M(Λ) ⊆ Λ` gives a holomorphic endomorphism fixing 0, algebraic by GAGA, a homomorphism by rigidity, unique because a reduced finite-type `ℂ`-scheme is determined by its `ℂ`-points; part 2: the analytic representation. Holds for every weak uniformization, by the `Φ = π∘L` argument | yes | none | OK |
| `T11b_Rigidity` | `Hom_k(A, B) = Hom_L(A_L, B_L)` for `k = k̄` (Conrad 2006 §3, UNVERIFIED number); characteristic 0 is superfluous, which only weakens the statement *(review)* | yes | none | OK |
| `T12_ComplexConjEigen` (glue target, not a leaf) | true: `V_ℓ` has rank `2g`, `c` is an involution anticommuting with the complex structure on `Λ ⊗ ℝ`; `finrank` of finite-dimensional kernels, so no junk | — | — | true |

Notes to the table:
1. **R18.**
   - `IsBelyiFunction` says the maximal ideal of every place over a finite place other than
     `t = 0, 1` is generated by `q(t)`, i.e. `e = 1`; `∞` is left free; the trivial valuation ring
     is harmless since `q(t) ≠ 0`.
   - Over `K` this implies the condition over `ℚ̄`: constant field extensions are unramified in
     characteristic 0, and `K` is algebraically closed in `K(X)`.
   - `[K(X):K(t)] = [ℚ̄(X):ℚ̄(t)] ≥ deg_B`, and the bound is monotone in `d`
     (`javanpeykarBound_mono`).
   - `dim J = genus` follows through the Albanese property.
   - The `K`-point and the `K`-rationality of `t` only restrict the instances.
2. **R22.**
   - With `IsSiegel Ω`, `IsPeriodMatrix Λ Ω` gives a `ℂ`-linear `T` with `T(Λ) = Ωℤ² + ℤ²`, so
     `(Im Ω)⁻¹` pulls back to a principal polarization of `ℂ²/Λ`. Conversely every principal
     polarization with a symplectic basis arises this way. So the quantifier ranges over principal
     polarizations, which are algebraic over `ℚ̄` by GAGA and rigidity of `NS`.
   - `thetaConst` is the classical `θ[a/2; b/2](0, Ω)`, absolutely summable on `𝔥₂`.
   - `absLogHeight` uses sup norms (`≤` Pazuki's Euclidean `h_Θ`) and is invariant under scaling
     by `c ≠ 0` and under the choice of `emb`.
   - `pazukiC2 = 1000·2⁴·(log 2⁴)⁵ = C₂(2, 2)`.
   - `X ≥ max(1, x + log π)` is `X ≥ max(1, h_D)` for surfaces.
3. **R3.**
   - At `j ≠ 0, ∞` this is Lin–Yang's assertion with the polarization forgotten.
   - At `j ∈ {0, ∞}` the tuple is `[12 : 6 : 4 : 0]` in `J` coordinates. I checked by hand that this
     is `[1 : 0 : 0 : 0]` in Igusa–Clebsch coordinates (`J₂ = 1/8`, `J₄ = 1/1536`,
     `J₆ = 1/221184`, which is `t·12, t²·6, t³·4` with `t = 1/96`). That is the image of the
     product locus (`χ₁₀ = 0`), so the surface is a product of elliptic curves.
   - The second disjunct is a scheme isomorphism `A.X ≅ E₁.X ⊗ E₂.X`, which is weaker than a
     group isomorphism. For non-simple `A` it holds unconditionally (Shioda–Mitani) *(review)*.
   - The statement is existential in `C`, so the several principal polarizations of `(A, ι)` do
     not affect it (rv-qm-polar §1.3).
   - `HasSexticModel` with `IsGenus2` determines `C`, because `y ∉ ℂ(x)` (the sextic is
     squarefree).
   - The `IC*` normalizations (`/48`, `/72`, `/12`) are the standard sums over 15, 10 and 60
     partitions, and the tuple gives `I₆ = 4608 j(5j + 4)`, consistent with `OnQMLocus`
     *(review)*.

## 6. What compiles

- `lake env lean scratch/h-decomposition/Leaves.lean`: exit 0, 194 s.
  - Errors: 0. Warnings: only the `sorry` (L21540, `HSyn.glueOutputs_of_leaves`) and linters.
  - Before the first compile, `lake build ZInQKernel.Hypotheses.JHeight
    ZInQKernel.Compiler.Precision.HeightConstant` was needed: the upstream `lean/` package
    `ZInQ` was unbuilt in this worktree.
  - Outputs: `scratch/leaf-adopt2/compile2.txt`, `compile3.txt`.
- New `#print axioms`, all `[propext, Classical.choice, Quot.sound]`:
  `ZInQ.LeafPush2.stableFaltingsHeight`, `R18_real`, `javanpeykarBound_pos`,
  `javanpeykarBound_mono`, `R22_plus3`, `isSiegel_I`, `linYangTuple_onQMLocus`,
  `onQMLocus_of_linYangTuple`, `linYang_j_eq`, `R03_of_algClosed`, `exists_isComplexConj`,
  `T10_groupIso`, `R03_LinYang`, `R22_Pazuki`, `R18_Javanpeykar`,
  `HSyn.isComplexConj_leafPush2_iff`.

## 7. What remains

1. **Placeholders.**
   - R1(b): family form; needs analytification.
   - R17: fold def-ladic-cond's `LadicCond.CarayolR17'`, which leaf-push2 §4 confirmed as the form
     D5/G15-G16 need, with its glue Props. That would give 54 of 56.
   - T10: the Galois-equivariant form needs `ℤ_ℓ`-linear, functorial `EllAdicCohomology`.
     leaf-push2's `T10_groupIso` is in the file but is not the form used, so T10 stays a
     placeholder.
2. **Checks on the folded leaves.**
   - R22: read Pazuki's Def. 2.6.
   - R3: compare `LinYangTuple` with the printed (13)-(14) and with Baba–Granath Prop. 3.6.
   - Lemma P: read Buzzard p. 592 and Rotger.
   - AN3: makes R18-R22 and H5 non-vacuous.
3. **Glue targets.** `HeightCopiesAgree`, `T12_ComplexConjEigen`, `R03_LinYang_algClosed`, and
   the earlier ones (`X1ModelExists`, `BelyiX1`, `VSurjOfSurjective`, leaf-qm-fp §4).
4. **WP1 (unification).** `ZInQ.LeafPush2` adds second copies of:
   - the Arakelov layer and the stable height;
   - curves, Jacobians and Belyi functions (beside `LeafModCurves`);
   - `𝒪`, `QMStr` (beside `LeafQM`) and the Igusa–Clebsch invariants.
5. **`HSyn.glueOutputs_of_leaves`** (`sorry`).

h-decomposition.md §5 ends with this list as "Remaining work after leaf-adopt2".
