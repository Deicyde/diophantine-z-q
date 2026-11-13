# g0-fibresimple: `FibreSimple` reduced to four leaves and two glue Props; its quantifier makes it stronger than NoCM

Task g0-fibresimple, 2026-11-13. Lean: `scratch/g0-fibresimple/FibreSimple.lean`. It is
`scratch/g0-split/Split.lean` copied verbatim, followed by the new section `olean/Tail.lean`; it is
assembled by `assemble.sh`. While iterating, `Tail.lean` was compiled against an olean of the
copied prefix (`build_prefix.sh`, `ctail.sh`). Log: `scratch/g0-fibresimple/log.md`.

## 1. Result

**Main result.** g0-split's piece 4, `HSyn.G0Split.FibreSimple`, is proved in Lean with its
statement unchanged. The inputs are four leaves and two named glue Props:

```
theorem G0FibreSimple.fibreSimple_of_leaves (t : HSyn.TextbookLeaves) (hMul : MulIsogeny)
    (hRig : RigidityHom) (p : FibreSimplePieces) : HSyn.G0Split.FibreSimple
-- t supplies T6 (t.t6) and T27 (t.t27)
-- p bundles FS1b′ FiniteDescends and FS5 FibreComTrivial
```

**Verification.** VERIFIED (compiled): `lake env lean scratch/g0-fibresimple/FibreSimple.lean`
exits 0 with no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
every new theorem (§4).

**The finding (§2).** FibreSimple quantifies over every moduli datum `(Y, Φ, π)` that satisfies
the clause lists `R1fpProps` and `R2fpProps`. These clauses do **not** determine the moduli
bijection `Φ` on closed points. This is proved in Lean (`r1fpProps_twistBy`,
`r2fpProps_twistBy`).

As a result, FibreSimple, and its glue piece FS5, assert more than NoCM for the true Shimura curve
`Y₃`. They also need an arithmetic non-coincidence that is not a published theorem and is not
decided here. So **FibreSimple is not shown false, but it is not a consequence of the published
leaves as stated**. §3 proposes a repair to the leaf R1, which leaves FibreSimple's text as it
is.

### Leaves

| name | statement | source | where |
|---|---|---|---|
| T27 `PkgI3.QMDichotomyYu` | QM dichotomy: `End⁰ ≅ B` or `M₂(ℚ(√d))` | Yu, JPAA 2013, Thm 1.1 | `TextbookLeaves.t27` |
| T6 `PkgI3.HomFreeFinite` | `Hom(A, B)` is a free `ℤ`-module of finite rank | Mumford §19 Thm 3 | `TextbookLeaves.t6` |
| `MulIsogeny` (**new**) | for `n ≠ 0`, `[n]` is finite and surjective (char 0) | Mumford §4 Application 2 (over `k̄`); Milne, *Abelian varieties* (Cornell–Silverman 1986) Thm 8.2, over any field (locators UNVERIFIED) | new; the degree `n^{2g}` is dropped |
| `RigidityHom` (**new**) | a `k`-morphism of abelian varieties with `h(0) = 0` is a homomorphism | Mumford §4 Cor. 1; Milne Cor. 2.2, over any field (locators UNVERIFIED) | new |

### Glue

| name | step | statement | status |
|---|---|---|---|
| `B6_isUnit` | G5 (Yu's hypothesis) | `B = (2,-3)_ℚ` is a division algebra | **proved** (from `GlueDescent.aniso_rat`) |
| `qm_embeds_end0` | G5 (Yu's hypothesis) | a QM structure gives `ℍ[ℚ,2,-3] →ₐ[ℚ] End⁰(A)` | **proved** (`QuaternionAlgebra.Basis.liftHom` on `1⊗ι(i)`, `1⊗ι(j)`) |
| FS4 `CentralizerOfMatrixEnd0` | G6, algebra | `End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0` ⇒ `com q` contains a non-integer | **proved from T6** (`centralizerOfMatrixEnd0_of_homFree`) |
| FS3 `EndDivisionOfEnd0Division` | G5 ⇒ simple | `End⁰(A)` a division ring ⇒ nonzero endomorphisms are isogenies | **proved from T6, `MulIsogeny`** (`end0Division_of_homFree`) |
| FS2 `EndDivisionOfSchemeIso` | rigidity | `A.X ≅ B.X` as `k`-schemes, `EndDivision B` ⇒ `EndDivision A` | **proved from `RigidityHom`** (`endDivisionOfSchemeIso_of_rigidity`) |
| FS1 `EndDivisionDescent` | model `A/K` | `EndDivision(A_L) ⇒ EndDivision(A)` | **proved from FS1a, FS1b** (`endDivisionDescent_of`) |
| FS1a `BaseChangeFaithful` | scheme theory | `Over.pullback (Spec L → Spec K)` is faithful | **proved** (`baseChangeFaithful_proof`, from Mathlib's fpqc instance in `Morphisms/FlatDescent.lean`) |
| FS1b `IsogenyDescends` | scheme theory | "finite and surjective" descends along `Spec L → Spec K` | **proved from FS1b′** (`isogenyDescends_of`; surjectivity via the base-change square) |
| FS1b′ `FiniteDescends` | scheme theory | `IsFinite` descends along `Spec L → Spec K` | **glue, unproved**. STANDARD (EGA IV₂ 2.7.1, UNVERIFIED). Mathlib v4.35 has `RingHom.Finite.codescendsAlong_faithfullyFlat` and `HasAffineProperty.descendsAlong_of_affineAnd`, but not the descent of `IsAffineHom` the latter needs |
| FS5 `FibreComTrivial` | G6, NoCM | for `u ∉ 𝒞` and an object `P` at a `ℚ̄`-point over `J(u)`, `End_𝒪(P.A) = ℤ` | **glue, unproved; carries the gap of §2** |

### Proof of FibreSimple

`FibreOver` gives an embedding `K → ℚ̄`, a point `y` over `J(u)`, an object `P` and an iso of
`ℚ̄`-schemes `A_ℚ̄ ≅ P.A`. The proof then runs as follows.

1. T27 at `B = (2,-3)` (`PkgI3.qmDichotomy_B6`, with `B6_isUnit`, `qm_embeds_end0`, `P.surface`)
   gives `End⁰(P.A) ≅ B` or `≅ M₂(ℚ(√d))`.
2. The second case is impossible: FS4 gives a non-integer in `com P.q`, and FS5 says
   `com P.q = ℤ`.
3. Since `End⁰(P.A) ≅ B` is a division ring, FS3 makes every nonzero endomorphism of `P.A` an
   isogeny.
4. FS2 moves this to `A_ℚ̄`, and FS1 moves it down to `A`.

**How the proved pieces go.**

- **FS4.** The scalar matrix `√d` is central in `M₂(ℚ(√d))`, so its preimage `c'` is central in
  `End⁰(A)`, and `c'` is not rational because `(√d)² = d < 0`. Since `ℚ ⊗ End(A)` is the
  localization of `End(A)` (Mathlib `isLocalizedModule_iff_isBaseChange`), `s·c' = 1 ⊗ φ` for
  some `φ` and some `s ≠ 0`. Freeness (T6) makes `m ↦ 1 ⊗ m` injective, so `φ ∈ com q` and `φ`
  is not an integer.
- **FS3.** Clearing denominators in `(1⊗f)⁻¹` gives `g ∘ f = f ∘ g = [s]`. Then Mathlib's
  `IsFinite.of_comp` (`g` is separated because `A` is proper) and `Surjective.of_comp` apply.
- **FS2.** Set `ψ = e − e(0)` and `ψ' = e⁻¹ ∘ (· + e(0))`, using the group of morphisms into the
  group object. They are mutually inverse and preserve `η`, so rigidity makes them homomorphisms.
  Conjugating by them finishes the proof.
- **FS1.** Base-changing `f` gives a homomorphism (`Functor.map.instIsMonHom`). It is nonzero
  because the functor is faithful and `F(1) = 1` (`Functor.map_one`). Being an isogeny then
  descends.

**Truth of FS1b′ and the two new leaves.** These are model checks with no human review. All
three are textbook facts. Each docstring in `Tail.lean` gives its argument.

## 2. Finding: `R1fpProps`, `R2fpProps` do not pin down `Φ`

**Proved in Lean.** Let `σ` be a natural automorphism of the field-point functor
`K ↦ (fieldPt K ⟶ Y)` (`PtAuto Y`).

- `(Y, Φ ∘ σ, π)` satisfies `R1fpProps` whenever `(Y, Φ, π)` does (`r1fpProps_twistBy`, no
  condition).
- It satisfies `R2fpProps` if `σ` permutes the `π`-fibres of `ℚ̄`-points and fixes the fibres over
  `0, ∞, −16/27` (`r2fpProps_twistBy`).
- `fibreComTrivial_twisted` spells out what FS5 asserts about the given data when it is applied to
  the twisted data.

VERIFIED (compiled).

**Why such `σ` exist (argument, STANDARD scheme theory).**

- A `K`-point of a `ℚ`-scheme is a point `p` together with an embedding `κ(p) → K`.
- A bijection `s` of closed points, with `ℚ`-isomorphisms `κ(s p) ≅ κ(p)`, therefore defines a
  natural automorphism of all field points. It is the identity on non-closed points.
- Take the true data `(Y₃, Φ, π)` and two rational non-branch values `t₁ = J(u)`, `t₂`. Suppose
  their fibres are isomorphic `Gal(ℚ̄/ℚ)`-sets, that is, their closed points match with
  isomorphic residue fields. Then swapping the two fibres gives such a `σ`, and it satisfies the
  hypotheses of `r2fpProps_twistBy`.

**Consequence.** Suppose also that `t₂` is a CM value. At `(Y₃, Φ ∘ σ, π)`, the object over a point
over `J(u)` is then a CM surface. A model of it over a number field over which all its
endomorphisms are defined is not simple, so FibreSimple fails for this datum.

The swap must send the `Gal`-stable fibre over `J(u)` to a single fibre, so `t₂ ∈ P¹(ℚ)`. Given
NoCM for the true data, FibreSimple is therefore equivalent to:

> no `u ∉ 𝒞` and no rational non-branch CM value `t₂ ∉ {0, ∞, −16/27}` have isomorphic Galois
> sets `π⁻¹(J(u))(ℚ̄) ≅ π⁻¹(t₂)(ℚ̄)`.

**Status of this condition: SPECULATIVE / not decided.**

- If `Y₃ → P¹` is Galois with group `Γ'` acting over `ℚ` (R1hecke), the condition says the two
  specialization fields differ.
- For a fixed `t₂`, the values `t` with the same specialization field are rational points on
  twists of `Y₃`. There are finitely many if the genus is at least 2 (my Riemann–Hurwitz
  estimate of `g(Y₃)` is 7, SPECULATIVE).
- Whether one of them is some `J(u)` with `u ∉ 𝒞` is uncomputed. A coincidence is unlikely, but
  no published theorem excludes it.
- The NoCM argument of rv-h-cm §7.2 does not help. It uses `X₆`-level data (residue field `ℚ(i)`,
  free `W`-orbit), which is not among FibreSimple's hypotheses, and the twisted `Φ` lives on `Y₃`.

**Other pieces.** Pieces 9 (`ThetaPointOfFibre`) and 10 (`ModularConstituent`) of g0-split
quantify over `(Y, Φ, π)` in the same way. Their truth at twisted data was not checked
(SPECULATIVE).

## 3. Proposed repair (not applied: these are other tasks' files)

**Recommended: add a family clause to the leaf R1.** The clause would say: there is an abelian
scheme `𝒜 → Y` with QM by `𝒪` and level-3 structure such that `Φ K y` is the class of `y*𝒜`
(WP12's "R1(b) in family form").

- With the clause, the classifying map `Y → Y₃` of `𝒜` (universal property of the fine moduli
  scheme) is bijective on `K`-points for every field `K`.
- Between smooth proper curves over `ℚ`, such a map is finite, birational and universally
  injective, hence an isomorphism. So `Φ` is the true bijection transported along `Y ≅ Y₃`
  (STANDARD argument, not formalized).
- `R2fpProps` then pins down `π` as the Hauptmodul, by its values at the three CM points
  (g0-split §3).
- FS5 then follows from NoCM for the true data (rv-h-cm §7.2), and FibreSimple's text is
  unchanged.
- The published input is fine moduli for `Y₃` with neat level-3 structure (Buzzard, Duke 1997,
  is the usual reference; UNVERIFIED).

**Alternative.** A specialization clause in field-point form: for a DVR `R` and `Spec R → Y`, the
object at the generic point has good reduction with special fibre the object at the closed point,
using PkgI2's abelian schemes. Adding the §2 condition as a hypothesis is not recommended: it is a
computation, not a published theorem.

## 4. What compiles, what remains

- Compiles (VERIFIED): `scratch/g0-fibresimple/FibreSimple.lean` (Split.lean verbatim + Tail)
  with `lake env lean`: exit 0, no errors, no `sorry` (see the log for time and size).
  `#print axioms` gives the standard three for `HSyn.glueOutputs_of_leaves` and for each of
  `B6_isUnit`, `qm_embeds_end0`, `centralizerOfMatrixEnd0_of_homFree`,
  `end0Division_of_homFree`, `endDivisionOfSchemeIso_of_rigidity`, `endDivisionDescent_of`,
  `baseChangeFaithful_proof`, `isogenyDescends_of`, `fibreSimple_of_pieces`, `…'`, `…''`,
  `fibreSimple_of_leaves`, `r1fpProps_twistBy`, `r2fpProps_twistBy` and
  `fibreComTrivial_twisted`.
- Remains:
  - FS1b′ (finiteness descends along a field extension). This is Mathlib-level work: the fpqc
    descent of `IsAffineHom`, after which `HasAffineProperty.descendsAlong_of_affineAnd` with
    `RingHom.Finite.codescendsAlong_faithfullyFlat` gives it.
  - FS5 (NoCM on the actual fibre). It needs the R1 repair of §3. It then still needs the Kummer
    model of `X₆ → P¹`, González–Rotger (R5) and the count of rv-h-cm §7.2.
- Integration: append `olean/Tail.lean` (minus its import line) after g0-split's section.
  - Replace `fibreSimple` in `G0Split.MissingPieces` (or leaf-adopt3's `GluePieces`) by
    `FibreSimplePieces` (FS1b′, FS5).
  - Add `MulIsogeny` and `RigidityHom` to `TextbookLeaves`.
  - `fibreSimple_of_leaves` then gives the old field.
