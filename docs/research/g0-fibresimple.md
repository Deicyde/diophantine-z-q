# g0-fibresimple: g0-split's piece 4, `FibreSimple`, reduced to four leaves and two glue Props; a gap in its quantifier

Task g0-fibresimple, 2026-11-13. Lean: `scratch/g0-fibresimple/FibreSimple.lean`. It is
`scratch/g0-split/Split.lean` copied verbatim, followed by the new section `olean/Tail.lean`; it is
assembled by `assemble.sh`. While iterating, `Tail.lean` was compiled against an olean of the
copied prefix (`build_prefix.sh`, `ctail.sh`). Log: `scratch/g0-fibresimple/log.md`.

## 1. Result

**Main result.** `HSyn.G0Split.FibreSimple` is proved in Lean. The statement is unchanged. The
proof uses four leaves and two named glue Props:

```
theorem G0FibreSimple.fibreSimple_of_leaves (t : HSyn.TextbookLeaves) (hMul : MulIsogeny)
    (hRig : RigidityHom) (p : FibreSimplePieces) : HSyn.G0Split.FibreSimple
-- p bundles FS1 EndDivisionDescent and FS5 FibreComTrivial
```

There is also a form with each input as its own hypothesis:

```
theorem fibreSimple_of_pieces'' (t6 : PkgI3.HomFreeFinite) (t27 : PkgI3.QMDichotomyYu)
    (hMul : MulIsogeny) (h1 : EndDivisionDescent) (h2 : EndDivisionOfSchemeIso)
    (h5 : FibreComTrivial) : FibreSimple
```

**Verification.** VERIFIED (compiled): `lake env lean scratch/g0-fibresimple/FibreSimple.lean`
exits 0 with no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
every new theorem.

**The finding (§2).** FibreSimple quantifies over every moduli datum `(Y, Φ, π)` that satisfies
the clause lists `R1fpProps` and `R2fpProps`. These clauses do **not** determine the moduli
bijection `Φ` on closed points. This is proved in Lean (`r1fpProps_twistBy`,
`r2fpProps_twistBy`).

As a result, FibreSimple asserts more than NoCM for the true Shimura curve `Y₃`. It also needs an
arithmetic statement that is not a published theorem and is not decided here: no rational CM value
`t₂` has a `π`-fibre isomorphic, as a Galois set, to the fibre over some `J(u)`. So FS5, and with
it FibreSimple, is **not known to follow from the published literature as stated**.

- I could not exhibit a counterexample, so the piece is **not shown false**.
- A repair is proposed in §3: add a family clause to the leaf R1. With it, the piece becomes a
  consequence of the published mathematics.

### Leaves used

| name | statement | source | status |
|---|---|---|---|
| T27 `PkgI3.QMDichotomyYu` | QM dichotomy `End⁰ ≅ B` or `M₂(ℚ(√d))` | Yu, JPAA 2013, Thm 1.1 | in `TextbookLeaves.t27` |
| T6 `PkgI3.HomFreeFinite` | `Hom(A, B)` is a free `ℤ`-module of finite rank | Mumford §19 Thm 3 | in `TextbookLeaves.t6` |
| `MulIsogeny` (**new**) | for `n ≠ 0`, `[n]` is finite and surjective (char 0) | Mumford §4, Application 2 (over `k̄`); Milne (Cornell–Silverman 1986) Thm 8.2, over any field (locators UNVERIFIED) | new textbook leaf; Mumford's statement with the degree `n^{2g}` dropped |
| `RigidityHom` (**new**) | a `k`-morphism of abelian varieties with `h(0) = 0` is a homomorphism | Mumford §4 Cor. 1; Milne (Cornell–Silverman 1986) Cor. 2.2, over any field (locators UNVERIFIED) | new textbook leaf |

### Glue pieces

| name | step | statement | status |
|---|---|---|---|
| `B6_isUnit` | G5 (Yu's hypothesis) | `B = (2,-3)_ℚ` is a division algebra | **proved** (from `GlueDescent.aniso_rat`) |
| `qm_embeds_end0` | G5 (Yu's hypothesis) | a QM structure `ι : 𝒪 → End(A)` gives `ℍ[ℚ,2,-3] →ₐ[ℚ] End⁰(A)` | **proved** (`QuaternionAlgebra.Basis.liftHom` on `1⊗ι(i)`, `1⊗ι(j)`) |
| FS4 `CentralizerOfMatrixEnd0` | G6, algebra | if `End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, then `com q` contains a non-integer | **proved from T6** (`centralizerOfMatrixEnd0_of_homFree`) |
| FS3 `EndDivisionOfEnd0Division` | G5→simple | `End⁰(A)` a division ring ⇒ every nonzero endomorphism is an isogeny | **proved from T6 + `MulIsogeny`** (`end0Division_of_homFree`) |
| FS1 `EndDivisionDescent` | model `A/K` | `EndDivision(A_L) ⇒ EndDivision(A)` for a field extension `L/K` | glue, unproved (descent of "finite, surjective" along `Spec L → Spec K`; faithfulness of base change) |
| FS2 `EndDivisionOfSchemeIso` | rigidity | `A.X ≅ B.X` as `k`-schemes and `EndDivision B` ⇒ `EndDivision A` | **proved from `RigidityHom`** (`endDivisionOfSchemeIso_of_rigidity`: translate `e` by `-e(0)`, then conjugate) |
| FS5 `FibreComTrivial` | G6, NoCM | for `u ∉ 𝒞` and every object `P` at a `ℚ̄`-point over `J(u)`, `End_𝒪(P.A) = ℤ` | glue, unproved; **carries the gap of §2** |

### Proof of FibreSimple from these

`FibreOver` gives an embedding `K → ℚ̄`, a point `y` over `J(u)`, an object `P` and an iso of
`ℚ̄`-schemes `A_ℚ̄ ≅ P.A`. The proof then runs as follows.

1. T27 at `B = (2,-3)` (`PkgI3.qmDichotomy_B6`, with `B6_isUnit`, `qm_embeds_end0`, `P.surface`)
   gives `End⁰(P.A) ≅ B` or `≅ M₂(ℚ(√d))`.
2. The second case is impossible: FS4 gives a non-integer in `com P.q`, and FS5 says
   `com P.q = ℤ`.
3. Since `End⁰(P.A) ≅ B` is a division ring, FS3 makes every nonzero endomorphism of `P.A` an
   isogeny.
4. FS2 moves this to `A_ℚ̄`, and FS1 moves it down to `A`.

**Truth of FS1 and of the two new leaves.** These are model checks with no human review. FS1,
`MulIsogeny` and `RigidityHom` are textbook facts about abelian varieties over fields. FS2, FS3
and FS4 are now Lean proofs from T6, `MulIsogeny` and `RigidityHom`. The docstrings in
`Tail.lean` give the arguments.

## 2. Finding: `R1fpProps`, `R2fpProps` do not pin down `Φ`

**What is proved in Lean.** Let `σ` be a natural automorphism of the field-point functor
`K ↦ (fieldPt K ⟶ Y)` (`PtAuto Y`). Then `(Y, Φ ∘ σ, π)` satisfies `R1fpProps` whenever
`(Y, Φ, π)` does (`r1fpProps_twistBy`, no condition). It also satisfies `R2fpProps` if `σ` permutes
the `π`-fibres of `ℚ̄`-points and fixes the fibres over `0, ∞, −16/27` (`r2fpProps_twistBy`).
`fibreComTrivial_twisted` spells out what FS5 asserts about the given data when it is applied to
the twisted data. VERIFIED (compiled).

**Why such `σ` exist (argument, STANDARD scheme theory).**

- A `K`-point of a `ℚ`-scheme is a point `p` together with a `ℚ`-embedding `κ(p) → K`.
- A bijection `s` between closed points with `ℚ`-isomorphisms `κ(s p) ≅ κ(p)` therefore defines a
  natural automorphism of all field points: it is the identity on non-closed points.
- Take the true data `(Y₃, Φ, π)` and two rational non-branch values `t₁ = J(u)`, `t₂`. Suppose
  their fibres are isomorphic as `Gal(ℚ̄/ℚ)`-sets, that is, closed points match with isomorphic
  residue fields. Then the swap of the two fibres is such a `σ`. It satisfies the hypotheses of
  `r2fpProps_twistBy`.

**Consequence.** Suppose in addition that `t₂` is a CM value. At `(Y₃, Φ ∘ σ, π)`, the object over
a point `y` over `J(u)` is then a CM surface. Take a model of it over a number field over which all
its endomorphisms are defined. That model is not simple, so FibreSimple fails for this datum.

So, given NoCM for the true data, FibreSimple is equivalent to:

> no `u ∉ 𝒞` and no rational non-branch CM value `t₂ ∉ {0, ∞, −16/27}` have isomorphic Galois
> sets `π⁻¹(J(u))(ℚ̄) ≅ π⁻¹(t₂)(ℚ̄)`.

The fibre over a non-CM rational value never lies over a CM point, and the swap must send the
`Gal`-stable fibre over `J(u)` to a single fibre, so `t₂ ∈ P¹(ℚ)`.

**Status of this condition: SPECULATIVE / not decided.**

- If `Y₃ → P¹` is Galois with group `Γ'` acting over `ℚ` (R1hecke), the condition says the two
  specialization fields differ. For each `t₂` there are only finitely many `t` with the same
  specialization field: these are rational points on twists of `Y₃`, and Faltings applies if the
  genus is at least 2. My estimate of the genus of `Y₃`, by Riemann-Hurwitz, is 7 (SPECULATIVE).
- Whether one of these `t` is a value `J(u)` with `u ∉ 𝒞` is a finite but uncomputed question.
- A coincidence is unlikely, but it is not excluded by any published theorem. So FS5 and
  FibreSimple are not consequences of the literature as stated.
- The NoCM argument of rv-h-cm §7.2 does not help here. Its X₆-level data (residue field `ℚ(i)`,
  free `W`-orbit) is not part of FibreSimple's hypotheses, and a wild `σ` acts on `Y₃` only.

**Other pieces.** Pieces 9 (`ThetaPointOfFibre`) and 10 (`ModularConstituent`) of g0-split
quantify over `(Y, Φ, π)` in the same way. Their truth at twisted data was not checked
(SPECULATIVE). For example, piece 9 at twisted data needs a point `z'` with `Φ_Igusa(z') = J(u)`
and height at most that of the theta-nulls of a surface lying over `t₂`.

## 3. Proposed repair (not applied: other tasks' files)

**Recommended: strengthen the leaf R1.** Add to `R1fpProps` a family clause, as in WP12's
"R1(b) in family form". It would say that there is an abelian scheme `𝒜 → Y` with QM by `𝒪` and
a level-3 structure such that `Φ K y` is the class of `y*𝒜`.

- With this clause, the classifying morphism `Y → Y₃` of `𝒜` (from the universal property of
  the fine moduli scheme `Y₃`) is bijective on `K`-points for every field `K`. Between smooth
  proper curves over `ℚ` it is then finite, birational and universally injective, hence an
  isomorphism. So `Φ` is the true moduli bijection transported along `Y ≅ Y₃` (STANDARD
  argument, not formalized). A point-level permutation `σ` that does not come from a morphism of
  `Y` cannot then keep `Φ` in this form.
- FS5 then follows from NoCM for the true data (rv-h-cm §7.2), and FibreSimple's text stays as it
  is.
- The published input is fine moduli for `Y₃` with level-3 structure: the level is neat, so the
  moduli problem is representable (Buzzard 1997 is the usual reference, UNVERIFIED). This is
  stronger than the field-point clauses, but it is still a published statement.

**Alternative.** Keep R1 and add the condition of §2 as an explicit hypothesis. It is not a
published theorem, so it would have to be a computation; it is not recommended.

## 4. What compiles, what remains

- Compiles (VERIFIED, `Tail.lean` against the prefix olean, exit 0): everything in §1-§2.
  `#print axioms` gives only the standard three for `B6_isUnit`, `qm_embeds_end0`,
  `centralizerOfMatrixEnd0_of_homFree`, `end0Division_of_homFree`,
  `endDivisionOfSchemeIso_of_rigidity`, `fibreSimple_of_pieces`,
  `fibreSimple_of_pieces'`, `fibreSimple_of_pieces''`, `fibreSimple_of_leaves`,
  `r1fpProps_twistBy`, `r2fpProps_twistBy` and `fibreComTrivial_twisted`.
- Standalone `scratch/g0-fibresimple/FibreSimple.lean` (Split.lean + Tail, 20474 lines),
  VERIFIED: `lake env lean` exits 0 in 174 s, with 0 errors and no `sorry`; the axioms are the
  standard three.
- Remains:
  - FS1 (descent of "every nonzero endomorphism is an isogeny" along a field extension). It
    needs two things: base change is faithful on homomorphisms, and "finite, surjective"
    descends. Mathlib's fpqc descent files (`Morphisms/FlatDescent.lean`, `EffectiveEpi.lean`)
    cover part of this; the bookkeeping for def-faltings' `baseChange` group structure is not
    done.
  - FS5 (NoCM on the actual fibre), which needs the R1 repair of §3. After the repair it still
    needs the Kummer model of `X₆ → P¹`, González–Rotger (R5) and the class-number count of
    rv-h-cm §7.2.
- Integration: append `olean/Tail.lean` (without its import line) after g0-split's section. In
  `G0Split.MissingPieces` (or leaf-adopt3's `GluePieces`), `fibreSimple` can then be replaced
  by `FibreSimplePieces` (FS1, FS5). The two textbook leaves `MulIsogeny` and `RigidityHom` go
  into `TextbookLeaves`, and T6, T27 are taken from there.
