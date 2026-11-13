# leaf-push2: concrete statements of R18, R22, R3; R17 confirmed; T10-T12

Task leaf-push2, 2026-11-12. Lean file: `scratch/leaf-push2/LeafPush2.lean` (one file, imports
`ZInQKernel.HDecomp.Objects` and Mathlib); log: `scratch/leaf-push2/log.md`.

## 1. Result

**13 of the 14 placeholders of `scratch/h-decomposition/Leaves.lean` now have concrete
statements somewhere in the repository (R1 only in parts (a), (c), (d); R1(b) is still
`opaque R01b_ComplexUniformization`); T10 is the one left.** This task adds R18, R22 and R3,
and replaces T11 and T12 by concrete textbook leaves over a new uniformization predicate. The
other nine come from earlier reports: R1, R2, R5 (leaf-qm-fp), R16 (leaf-modcurves), R17
(def-ladic-cond, now `LadicCond.lean`), R19-R21 (def-faltings).

- **R18 (Javanpeykar).** `R18_Javanpeykar` is stated over the stable Faltings height of
  def-faltings, the Albanese predicate `IsJacobian` and `IsBelyiFunction` of leaf-modcurves, with
  `g := dim J` (rv-blueprints recommendation 5). It is a CONSEQUENCE of the printed Thm 1.1.1
  together with H5 (rv-blueprints F2).
- **R22 (Pazuki).** `R22_Pazuki` is the audit's upper half: `h ≤ X/2 + C₂ log(X+2)` for every
  `X ≥ max(1, h_F + log π)`. It is stated for every abelian surface over a number field, every
  analytic uniformization at every complex place, and every `Ω ∈ 𝔥₂` that is a period matrix of
  the lattice. The height is that of the theta-null point `[θ[a;b](0, Ω)]`. One new definition
  carries the principal polarization: "`Ω` is a period matrix of `Λ`" (`IsPeriodMatrix`). No
  polarization object is needed (§3). CONSEQUENCE, with H5 and a GAGA/Riemann-form step.
- **R3 (Lin–Yang).** `R03_LinYang` is stated over `ℂ`. Every abelian surface `A` with
  `𝒪 ↪ End A` is either `≅ Jac(C)`, for a curve `C` with a sextic model on the Lin–Yang family at
  some `j ≠ 0`, or `≅ E₁ × E₂`. The statement is existential and polarization-free. It is a
  CONSEQUENCE of Example 29 plus Weil's dichotomy, and depends on the existence of a principal
  polarization of the fixed type (§3). The Igusa convention is checked in Lean:
  `linYangTuple_onQMLocus` proves that Lin–Yang's `J`-tuple (scaling `c²`) implies
  hdec-elementary's Igusa–Clebsch locus `OnQMLocus` (the direction F1 uses), the input of the proved F1 glue. So the two
  conventions in the repository agree, and the warning in locators.md ("fix the J/Igusa–Clebsch
  convention") is discharged for these two definitions.
- **R17.** `LadicCond.CarayolR17'` is confirmed as the concrete form D5/G15-G16 need, with no
  change (§4).
- **T10-T12** (§5):
  - T11 becomes two concrete textbook leaves (`T11a_RiemannEnd`, `T11b_Rigidity`) and T12 a glue
    target (`T12_ComplexConjEigen`, the eigenspace form G10 uses). T12 (glue) and the non-vacuity of
    T11a rest on one new textbook leaf, `UniformizationExists` (AN3 for abelian varieties);
    `T11a_RiemannEnd` takes `Φ` as a hypothesis and `T11b_Rigidity` does not involve it.
  - T10: Mathlib v4.35 **does** have `ℓ`-adic cohomology (pro-étale, `Scheme.EllAdicCohomology`),
    but only as an abelian group, with no `ℤ_ℓ`-structure and no functoriality. So only a
    non-equivariant group form is statable (`T10_groupIso`), not the Galois-equivariant form that
    is used.

Compile: `lake env lean scratch/leaf-push2/LeafPush2.lean` gives exit 0, no errors and no
warnings. Every `#print axioms` (15 lines, including the four leaf Props and every theorem
proved in this task, 10 of the file's 72 theorems) is `[propext, Classical.choice, Quot.sound]` (VERIFIED). No `sorry`.

The independent check is in §6.

## 2. Definitions (where they come from)

| Object | Source | New? |
| --- | --- | --- |
| `HermitianLattice`, `HodgeData`, `GroupModel`, `MetrizedModel`, `stableFaltingsHeight`, `stableFaltingsHeightDeligne`, H5 Props | def-faltings §§1-18, H5 section (copied) | no; `AbVar` replaced by kernel `PkgI3.AbVar` (identical fields, identical `baseChange`, `dim`) |
| `IsCurve`, `IsJacobian`, `JacobianExists`, `IsBelyiFunction` | leaf-modcurves §D, §E, §G (copied) | no |
| `ffStructMap`, `ffAlgebra` (`K → K(X)`) | | yes |
| `cptObj`, `CPts`, `cEvalAt`, `cDom`, `IsUniformization` | def-faltings §17 adapted from group models to `AbVar` | adapted |
| `IsSiegel`, `IsPeriodMatrix`, `Char2`, `thetaConst` | | yes |
| `absLogHeight`, `pazukiC2` | rv-loc-leaves `PazukiR22.lean` (copied) | no |
| `𝒪`, `QMStr` | leaf-qm-fp §0-§1 (copied) | no |
| `IC2..IC10`, `IsGenus2`, `OnQMLocus` | hdec-elementary §1 (copied) | no |
| `IgJ2..IgJ10`, `LinYangTuple`, `sextic`, `HasSexticModel` | | yes |
| `IsComplexConj` | | yes |

## 3. The leaves

### R18 (`R18_Javanpeykar`)

Statement: for a number field `K`, a smooth proper geometrically connected integral curve
`X/K` with a `K`-point `P₀`, its Jacobian `J` (`IsJacobian X P₀ J aj`), `g = dim J ≥ 1`, a Belyi
function `t ∈ K(X)` over `K`, and `d = [K(X) : K(t)] > 0`, we have
`stableFaltingsHeight J ≤ 13·10⁶ · g · d⁵` in `EReal`.

Why it is a consequence of ANT 8 (2014), Thm 1.1.1 (locators.md: smooth projective connected
`X/ℚ̄`, `g ≥ 1`, stable Jacobian height, any Belyi degree bounds `deg_B`):
- base change to `ℚ̄`: the Albanese property and the Belyi condition are preserved in
  characteristic 0;
- `javanpeykarBound_mono`: a Belyi map of degree `d` gives `deg_B ≤ d`;
- either normalization works (rv-blueprints §1.2);
- H5 (existence half: the Néron model over a semistable field is a metrized model with the
  published height). The `EReal` form asserts `h < ⊤`, which is part of that half.

`R18_real` gives the real-valued form.

Sanity (proved): `javanpeykarBound_pos` (the bound is not `≤ 0`) and `javanpeykarBound_mono`.

Not proved: non-emptiness of the hypotheses. That would need a curve with a Jacobian as an
`AbVar`; no nonzero `AbVar` can be constructed in Mathlib v4.35 (Objects.lean, `AbVar.zero`
docstring).

### R22 (`R22_Pazuki`)

Statement: for an abelian surface `A/K`, `K` a number field, with `stableFaltingsHeight A = x`
(real) and `X ≥ max(1, x + log π)`, and every `σ`, `Φ` (`IsUniformization σ Λ Φ`) and
`Ω ∈ 𝔥₂` with `IsPeriodMatrix Λ Ω`: every representative `z ∈ L^{16}` (`L` a number field,
`emb : L → ℂ`, `emb z = c·θ(Ω)`, `c ≠ 0`) has `absLogHeight z ≤ X/2 + C₂ log(X+2)`. The hardened
form `R22_plus3` (`X = max(1, x+3)`) is proved from it.

- **Principal polarization without a polarization object.** For `Ω ∈ 𝔥₂`, the torus
  `ℂ²/(Ωℤ²+ℤ²)` carries the principal polarization `(Im Ω)⁻¹`, and every principal polarization
  of `ℂ²/Λ` with a symplectic basis is of this form. So "for every `Ω ∈ 𝔥₂` with
  `T(Λ) = Ωℤ² + ℤ²`" ranges over all principal polarizations of `A(ℂ)_σ` (STANDARD;
  Birkenhake–Lange §8.1, UNVERIFIED number).
- **Why the Jacobian of a genus-2 curve does not suffice here.** The canonical polarization of
  `Jac C` is given by the intersection form on `H₁(C(ℂ), ℤ)`, which needs singular homology of
  curves. The period-matrix encoding is cheaper and covers all principal polarizations.
- **Choice of `Ω`.** The height does not depend on it: a change of symplectic basis permutes the
  `θ_m` up to eighth roots of unity and a common factor.
- **Sup norm.** The sup-norm height is `≤` Pazuki's Euclidean-norm `h_Θ`, so the stated bound is
  weaker than his.

Inputs disclosed in the docstring:
- H5;
- analytic principal polarizations are algebraic over `ℚ̄` (T11-type);
- the identification of Pazuki's level-2 theta coordinates (Def. 2.6) with the classical
  `θ[a;b](0, Ω)`, `a, b ∈ {0, ½}²`. This follows the project's earlier reading (h-decomposition
  R22, pkg-I5) and is **UNVERIFIED here: the main risk of this leaf.**

Sanity (proved): `isSiegel_I`, i.e. `𝔥₂ ≠ ∅`.

### R3 (`R03_LinYang`, over `ℂ`; `R03_LinYang_algClosed` is the glue target over any algebraically closed field of characteristic 0)

Statement: for `A : AbVar ℂ` of dimension 2 with `q : QMStr A`, one of two cases holds.
1. There are `j ≠ 0` and a sextic `a∏(x − rᵢ)` with distinct roots satisfying
   `LinYangTuple a r j`, and a curve `C` (`IsCurve`, integral) with function field
   `ℂ(x)[y]/(y² − a∏(x−rᵢ))`, whose Jacobian is `≅ A` as group schemes.
2. `A ≅ E₁ × E₂` with `dim Eᵢ = 1` (a scheme isomorphism `A.X ≅ E₁.X ⊗ E₂.X`, no `IsMonHom`).

The hypothesis `dim A = 2` is needed: `B × B` of dimension 4 also has QM by `𝒪`.

- **Consequence of.** Lin–Yang Example 29 (arXiv v1) at `j ≠ 0, ∞`. At `j ∈ {0, ∞}`, the
  tuple has `J₁₀ = 0`, and Weil's dichotomy for principally polarized abelian surfaces gives a
  product (Weil 1957, UNVERIFIED).
- **Depends on.** `(A, ι)` carries a principal polarization of the fixed type (bp-qmmoduli §2.2,
  SPECULATIVE in the repository). The same dependency as leaf-qm-fp's leaves.
- **What the stated form omits.** It does not give the link "`j` = the value `π₆(x)` of the moduli
  point", which F1 uses. That link needs leaf-qm-fp's `X₆` package and was not done here; F1's
  algebra is already reduced to `OnQMLocus` (`linYang_j_eq`, proved).

Proved: `linYangTuple_onQMLocus`, `onQMLocus_of_linYangTuple`, `linYang_j_eq`
(`j = 3779136·I₁₀²/I₄⁵`), `R03_of_algClosed`.

### Polarization (rv-qm-polar): which statements would change if a QM surface carried several principal polarizations

- `R22_Pazuki`: **no**. It quantifies over all principal polarizations, through all period
  matrices.
- `R03_LinYang`: **no**. It is existential in `C` and mentions no polarization. Each principal
  polarization gives a Jacobian structure, and Lin–Yang's is one of them.
- Two forms not stated here **would** change:
  - a universal form "every genus-2 `C` with `Jac C ≅ A` lies on the family". This is false if
    `A` has a principal polarization of another type.
  - the coordinate-linked form `j = π₆(x)`. It needs "the" polarization of the fixed type, so it
    needs uniqueness, or the moduli point must carry the polarization.
- `R18_Javanpeykar` and `T*`: not affected.

## 4. R17: `LadicCond.CarayolR17'` confirmed

- **Statement.** For every prime `ℓ` (including 2), every `ιC`, `ιL`, newform `f` of weight 2 and
  level `N > 0` with character `χ`, every semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to
  `f` (trace form at `p ∤ Nℓ`) and every prime `p ≠ ℓ` (including `p | N`):
  `condExp(ρ|_{G_{ℚ_p}}) = v_p(N)`.
- **This is the form D5/G16 consume.** The bound on the conductor of Glazer's `r_ℓ` (G15) bounds
  `v_p(N)` for `p ≠ ℓ`; `p = ℓ` is covered by a second prime `ℓ'`, which the quantifier over all
  `ℓ` allows.
- **Faithful to Théorème A** as locators.md reads it (all finite `p`, all coefficient places of
  other residue characteristic, `ℓ = 2` included; no discrete-series hypothesis over `ℚ`):
  - `condExp = codim V^{I_p} + Sw` is computed on the ℓ-adic `ρ` itself, which equals the
    conductor of its Weil–Deligne representation (STANDARD);
  - a semisimple `ρ` with the traces of `f` is `≅ ρ_{f,λ}` (Chebotarev and Brauer–Nesbitt);
  - duals do not change the conductor.
- **Glue Props left open.** `SwanIndependent` and `AdaptedExists` stay open as glue. They are
  needed only to pass to the every-level form `CarayolR17`, not for `CarayolR17'` itself,
  because `swan` makes a choice of level.
- No correction.

## 5. T10-T12: least definitions and libraries

| Leaf | Least definitions for a concrete statement | In a Lean library? | Done here |
| --- | --- | --- | --- |
| T10 `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨`, `G_K`-equivariant | ℓ-adic cohomology of a scheme; its `ℤ_ℓ`-module structure; pullback along morphisms (for the `G_K`-action through `A_K̄ → A_K̄`); `T_ℓ A` (kernel) | **Mathlib v4.35 has `Scheme.EllAdicCohomology X ℓ n`** (pro-étale, Bhatt–Scholze Def. 6.8.1) as an `AddCommGroup` only (VERIFIED, `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`); no module structure, no functoriality, no comparison with étale cohomology. The Stacks Lean library has an étale cohomology chapter (prereq-survey, unreviewed). prereq-survey's "missing" is out of date | `T10_groupIso`: `H¹_proet(A_K̄, ℤ_ℓ) ≃+ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)`, a non-equivariant consequence (Milne Thm 15.1(a) with the pro-étale/étale comparison; UNVERIFIED numbers). **Not the form used**; T10 stays open |
| T11 Riemann/GAGA/rigidity | complex points `A(ℂ)_σ`; analytic uniformization (`IsUniformization`); for rigidity only base change of morphisms | Mathlib: schemes, `Over.pullback`, holomorphy (`DifferentiableOn ℂ`); Tau Ceti: Riemann forms = polarizations (prereq-survey); GAGA nowhere | `UniformizationExists` (Mumford §1 + GAGA); `T11a_RiemannEnd` (`End A` = ℂ-linear maps preserving `Λ`); `T11b_Rigidity` (`Hom(A_L, B_L) = Hom(A, B)` over `k = k̄`, char 0). Concrete leaves, textbook |
| T12 Artin comparison with complex conjugation | as T11, plus complex conjugation in `G_ℚ` (`IsComplexConj`) | as T11; SGA 4 XI nowhere | `T12_ComplexConjEigen` (the form G10 uses: `±1`-eigenspaces of `c` on `V_ℓ(A)` have dimension `dim A`). Glue target from `UniformizationExists` + T5 (`A(ℚ̄)[ℓⁿ] = A(ℂ)[ℓⁿ] = Φ(ℓ⁻ⁿΛ)/Λ`) + linear algebra (`ℂ^g = W ⊕ iW`); no comparison theorem in étale cohomology is needed for abelian varieties. `exists_isComplexConj` proved |

## 6. Independent check

One read-only model review (subagent, 2026-11-12) checked every statement against
h-decomposition.md, locators.md and rv-blueprints.md, given the code but not this report's
conclusions. **Verdict: no DEFECT.** No statement is false, stronger than its source as
described, or vacuous. This is a model review, not a human review.

**What the reviewer confirmed:**
- **R18.**
  - `IsBelyiFunction` is the Belyi condition: places over finite places of `K(t)`, `e = 1`, `∞`
    left free.
  - `e = 1` over `K` is `e = 1` over `ℚ̄`, and `finrank K⟮t⟯ K(X)` is the degree over `ℚ̄`.
  - The `K`-point and the `K`-rational Belyi function only weaken the statement.
- **R22.**
  - `IsUniformization` forces `Φ = exp ∘ T` with `Λ` a lattice.
  - `IsSiegel` + `IsPeriodMatrix` = principal polarization + symplectic basis.
  - The theta constants are standard, the sup-norm height is `≤` the `ℓ²` height, and the height
    does not depend on the basis.
- **R3.**
  - The IC normalizations are the standard 15/10/60-term sums, and the J/I conversion is Igusa's.
  - The weights 1, 2, 3, 5 are right.
  - The product locus `[I₂:I₄:I₆:I₁₀] = [1:0:0:0]` is the J-point `[12:6:4:0]`. That is the tuple
    at `j = 0` and at `j = ∞`, so the second disjunct is coherent (reviewer, from memory:
    UNVERIFIED).
- **T11a, T11b, T12, `UniformizationExists`:** true. T10's coefficient sheaf `C(U, ℤ_ℓ)` is the
  right one.
- **R17.** `CarayolR17'` is faithful and is the form D5/G15-G16 need. `inertiaSet`, `wildSet`,
  `ramSet`, `swanAt` and `condExp` were checked; `condExp` equals the Weil–Deligne conductor.

**RISKs and what was done:**
1. **R18 normalization.** "Either normalization" covers only Faltings'/Deligne's. A normalization
   without `2^{-g}` would make the stated form stronger. Low risk (the audit read the stable
   Faltings height). *Done:* the docstring now says this explicitly.
2. **R22: Pazuki's level-2 coordinates.** The coordinates of Def. 2.6 must be `θ[a;b](0,Ω)`, not
   `θ(0,2Ω)` or squares. The leaf is a consequence only if Pazuki's `h_Θ ≥ h([θ[a;b](0,Ω)])`.
   Already disclosed as UNVERIFIED. *Open:* read Def. 2.6.
3. **R3: tuple and J-convention.** These are checked only against hdec-elementary's
   transcription (`linYangTuple_onQMLocus`), not against Lin–Yang or Baba–Granath. *Open:* compare
   with the printed (13)-(14).
4. **T10: `ℓ = char K`.** The statement allowed `ℓ = char K`, outside Milne's hypothesis. *Done:*
   added the hypothesis `(ℓ : K) ≠ 0`, which weakens the statement.

**NOTEs and what was done:**
- `T11a` did not tie `g` to `dim A`; it was true anyway. *Done:* added `A.dim = g`.
- `T12` also needs T26 and antiholomorphy. *Done:* added to the docstring.
- `IsComplexConj` duplicates `PkgI4.IsComplexConj`. *Done:* noted in the docstring.
- `CarayolR17'` depends on `SwanIndependent`/`AdaptedExists`, through the choice in `swan`, and on
  Casselman's `a(π_p) = v_p(N)`. Both are disclosed already.
- The reviewer's own argument (Λ = 𝒪v, class number 1, `E_μ(αv, βv) = tr(μ⁻¹αβ̄)`) supports the
  existence of a principal polarization of the fixed type, which R3 assumes. This is a model
  argument, not a source; the repository label stays SPECULATIVE pending rv-qm-polar.

Recompiled after these edits (§1).

## 7. What remains

- **R3:** the coordinate-linked form `j = π₆(x)` over leaf-qm-fp's `X₆` package.
- **T10:** the Galois-equivariant form. It needs `ℤ_ℓ`-linearity and functoriality of Mathlib's
  `EllAdicCohomology`.
- **Non-vacuity of R18, R22, R3.** Every one needs a nonzero `AbVar`, which cannot be
  constructed in Mathlib v4.35.
- **Glue proofs:** `T12_ComplexConjEigen` from `UniformizationExists` + T5; the Lefschetz glue
  `R03_LinYang_algClosed`.
- **Folding** into `Leaves.lean`. This is integration work; this task does not edit other tasks'
  files.
