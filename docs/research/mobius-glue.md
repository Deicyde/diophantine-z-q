# mobius-glue: the `π`-half of qm-pin's comparison, reduced to named facts

Task mobius-glue, 2026-11-13. Base 2dd83306 merged with `origin/wip/qm-pin`. Scratch:
`scratch/mobius-glue/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or another
task's directory was edited. Model work only, no human review.

## 1. Result

**`MobiusGlue` is proved in Lean from four named facts** (`scratch/mobius-glue/MobiusGlue.lean`,
compiled, 0 errors, axioms `[propext, Classical.choice, Quot.sound]`, VERIFIED):

```lean
theorem mobiusGlue_of_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) : MobiusGlue
```

The four facts:

| name | kind | content | status |
|---|---|---|---|
| `CurveRatFactor` | curves | on a proper smooth curve `S/ℚ`, if `ρ : S → P¹` is constant on the fibres of `σ : S → P¹` (on `ℚ̄`-points), then `ρ = R ∘ σ` at every `ℚ̄`-point with finite `σ`-value, for a rational function `R = [F : G]`, `F, G ∈ ℚ̄[t]` coprime | STANDARD (§3.1); not in Mathlib |
| `CurveSurj` | curves | a morphism `S → P¹` from a proper smooth curve over `ℚ` with a `ℚ̄`-point, whose fibres on `ℚ̄`-points are finite, is onto `P¹(ℚ̄)` | STANDARD (§3.2); not in Mathlib |
| `ObjBridge.TorsionStructure` | textbook leaf T5, already in the decomposition | `A(K̄)[n] ≅ (ℤ/n)^{2g}` (Mumford §4) | existing leaf of `TextbookLeaves` (h-decomposition T5) |
| `AutOInnerFinite` | algebra of the order `𝒪` | every ring automorphism of the kernel's `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely many | STANDARD (§3.3); not in Mathlib |

`MobiusGlue` is copied verbatim from `scratch/qm-pin/QMPin.lean`, with the qm-pin definitions it
uses: `QMFamily`, `IsFibreOf`, `R1famProps`, `R1fpPropsPin`, `R1univProps`, `R1fpPropsU`. A Python
string comparison confirmed that the text of each declaration is identical (VERIFIED).

Downstream, the comparison of two triples and the transfer of fibre statements now follow from the
named facts too. Both are compiled:

- **`sameTripleMor_of_named`**: two triples satisfying the fully repaired list are `SameTripleMor`.
- **`pointwise_of_witness_named`**: a fibre statement proved for the leaf's own triple holds for
  every triple. This is the form used by `FibreSimple`, `ThetaPointOfFibre` and
  `ModularConstituent`.

The CM-object hypothesis `hCM` stays as in qm-pin. It follows from the leaf bundle
(`cm_objects_of_R1R2fp`, qm-pin).

**What is proved, not assumed:**

1. **A Möbius map fixing `0, ∞, c` is the identity.** In Lean this is two theorems:
   - `Mob.natDegree_le_one_of_injective`: over an algebraically closed field of characteristic 0,
     a rational function `[F : G]` (`F`, `G` coprime) that is injective on `K` has `deg F ≤ 1` and
     `deg G ≤ 1`.
   - `Mob.ratEval_eq_self`: such a function with no finite pole, fixing `0` and some `c ≠ 0`, is
     the identity.
2. **The reduction `mobiusGlue_of_curveFacts`.** From the two curve facts and `TwistClassFinite`
   (finitely many classes in a twist class), the following steps are compiled:
   - the two maps `π'` and `π ∘ g` have the same fibres;
   - the CM points exist on `Y'`;
   - the fibres of `π ∘ g` are finite, so `π ∘ g` is onto `P¹(ℚ̄)` and the factor `R` is
     injective;
   - `R` has no finite pole (the fibre over `∞`) and fixes `0` and `−16/27`, so `R = id`, and
     `π' = π ∘ g` on `ℚ̄`-points.
3. **`TwistClassFinite` from `TorsionStructure` and `AutOInnerFinite`** (`twistClassFinite_of`).
   - `level3_finite`: in characteristic 0, given `TorsionStructure`, a pair `(A, ι)` carries only
     finitely many level structures. The proof goes through the kernel's `Level3.torsor`: a level
     structure is `a ↦ η₀(a u₀)`, and this depends only on `u₀ mod 3𝒪`.
   - `transportLevel` and `QML3.isoTransport` transport a level structure along an isomorphism of
     QM pairs.
   - `conjUnitIso`: the twists by `t` and by `v t v⁻¹` are isomorphic through `ι(v)`.

**Hypotheses of `MobiusGlue` that the proof uses:**

- for `Y'`: proper, smooth of relative dimension 1, with a `ℚ̄`-point; `Φ'` a bijection;
- both `R2fpProps`;
- the CM objects;
- `Φ' = Φ ∘ g`.

The proof does not use `R1fpPropsU Y Φ`, nor `R1famProps` or `R1univProps` of `Y'`. Those enter
only through `phi_part`, which produces `g`.

## 2. The statements (in `LeafQM.AV.Pin`)

```lean
def CurveRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ σ ρ : ToP1 S.left,
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        σ.val (K := Qbar) y.left = OnePoint.some t → ρ.val (K := Qbar) y.left = Mob.ratEval F G t

def CurveSurj : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    Nonempty (fieldPt Qbar ⟶ S) → ∀ σ : ToP1 S.left,
      (∀ y : fieldPt Qbar ⟶ S, {y' : fieldPt Qbar ⟶ S |
        σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite) →
      ∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = t

def TwistClassFinite : Prop :=
  ∀ P : QML3 Qbar, {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧
    ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}.Finite

def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)
```

`Mob.ratEval F G t` is `∞` if `G(t) = 0` and `F(t)/G(t)` otherwise: the value of `[F : G]` at a
finite point. The ingredients are all genuine definitions:

- the kernel's `ToP1` (a morphism to `P¹` by charts) and `ToP1.val` (its value at a field point,
  through Mathlib's `Scheme.SpecToEquivOfField`);
- `fieldPt`, `QML3`, `M3`, `QMIso` and `QMStr.twist` from `ZInQKernel/HDecomp/QM/`;
- Mathlib's `Polynomial`, `IsCoprime`, `IsProper` and `SmoothOfRelativeDimension`.

None of the four facts quantifies over an invented structure.

## 3. Why the named facts are true (argued; not compiled)

### 3.1 `CurveRatFactor`

Let `C` be a geometric component of `S_ℚ̄`: a smooth projective curve over `ℚ̄`, and there are
finitely many of them.

- **Case 1: `σ|C` is nonconstant.** Then `σ|C` is finite and surjective.
  - Let `D ⊆ P¹ × P¹` be the image of `(σ, ρ)|C`. It is closed (`C` is proper) and irreducible.
  - By the fibre condition, `pr₁ : D → P¹` is injective on points. It is also surjective.
  - In characteristic 0, `pr₁` is therefore finite of degree 1, hence birational. The inverse
    rational map `P¹ ⇢ D` extends to a morphism `s`, because `P¹` is a smooth curve and `D` is
    proper. By injectivity, `s ∘ pr₁ = id` on points.
  - So `ρ|C = (pr₂ ∘ s) ∘ σ|C`, where `R_C = pr₂ ∘ s : P¹ → P¹` is a rational function `[F : G]`
    with `F`, `G` coprime. (`R_C ≡ ∞` is `[1 : 0]`.)
- **Two nonconstant components agree.** Every `t ∈ ℚ̄` has preimages `c₁ ∈ C₁` and `c₂ ∈ C₂`. The
  fibre condition holds on all of `S`, so `R_{C₁}(t) = ρ(c₁) = ρ(c₂) = R_{C₂}(t)`, and
  `R_{C₁} = R_{C₂}`.
- **Case 2: `σ|C` is constant, equal to `t₀`.**
  - If some component is nonconstant, the fibre condition gives `ρ|C = ρ(c) = R(t₀)` for a point
    `c` over `t₀` on a nonconstant component.
  - If every component is constant, `σ` takes finitely many values. Choose `G = ∏ (t − tᵢ)` over
    the values `tᵢ` with `ρ = ∞`, and `F` by Lagrange interpolation with `F(tᵢ) ≠ 0` at those
    values.
- **References** (STANDARD; locators UNVERIFIED): Hartshorne II.6.8 (nonconstant implies finite
  and surjective), I.6.12 and II.6.7 (curves and function fields), IV.2 (separable degree equals
  the number of points of a generic fibre in characteristic 0).
- **Not in Mathlib v4.35.** Mathlib has `Scheme.functionField`, `PartialMap`, `RationalMap`,
  `Birational`, `OrderOfVanishing` and Zariski's main theorem (`AlgebraicGeometry/`, VERIFIED by
  listing). It has no `P¹` with its point bijection (as the kernel's `ToP1` docstring notes), no
  degree of a finite morphism of curves, and no "nonconstant morphism of curves is surjective".

### 3.2 `CurveSurj`

- Let `y₀` be the given `ℚ̄`-point and `C` its geometric component. `C` is an irreducible curve
  over `ℚ̄`, because `S` is smooth of relative dimension 1, so `C(ℚ̄)` is infinite.
- `σ|C` has finite fibres, so it is nonconstant. Its image is closed (`C` is proper), irreducible
  and not a point, so it is `P¹`.
- A closed point of `P¹_ℚ̄` has a closed preimage point with residue field `ℚ̄` (Nullstellensatz).
  That point is a `ℚ̄`-point of `S`.
- STANDARD (Hartshorne II.6.8; locator UNVERIFIED).

### 3.3 `AutOInnerFinite`

- A ring automorphism `α` of `𝒪` is `ℤ`-linear, so it extends to a `ℚ`-algebra automorphism of
  `B = 𝒪 ⊗ ℚ`, the quaternion algebra `(2, −3)` of discriminant 6.
- By Skolem–Noether, `α` is conjugation by some `x ∈ B^×`, and `x ∈ N(𝒪)`. Skolem–Noether is
  proved in the kernel (`TSkolemKW.skolemNoether`; `GlueDescent.B6_inner` gives exactly this
  form for `B6 = ℍ[ℚ, 2, −3]`).
- `N(𝒪)/ℚ^×𝒪^×` is finite. For a maximal order it is `⊕_{p | disc} ℤ/2`, here `W ≅ (ℤ/2)²`,
  generated by `i` (`nrd = −2`) and `j` (`nrd = 3`), both of which normalize `𝒪`. References:
  Vignéras, *Arithmétique des algèbres de quaternions*, Ch. II §1 and Ch. III §5; Voight,
  *Quaternion algebras*, normalizer chapter. Locators UNVERIFIED.
- STANDARD. In Lean this would be glue from Skolem–Noether plus the normalizer computation, which
  needs the two-sided ideals of `𝒪`; that is not attempted here.

### 3.4 Why some finiteness is needed

The finite-fibre input cannot be dropped. Suppose `π'` were constant on every geometric component
of `Y'`. Then the image of `π'` is finite, and `h` (with `π' = h ∘ π ∘ g`) is only some bijection
of that finite set fixing `0, ∞, −16/27`. No point-level argument excludes this.

Over the kernel's definitions, the fibre of `π'` through `y` is in bijection, via `Φ'`, with a
twist class. So `TwistClassFinite` is the natural form. Its proof needs both of the following:

- finitely many level structures per pair (`TorsionStructure`);
- finitely many pair classes per twist class (`AutOInnerFinite`).

The second is necessary: if `End(A) = ι(𝒪)`, the pair classes `(A, ι ∘ α)` correspond exactly to
`Aut(𝒪)` modulo inner automorphisms by units.

## 4. Lean outcomes (all VERIFIED; logs in `scratch/mobius-glue/log.md`)

| file | content | outcome |
|---|---|---|
| `RatInj.lean` | development copy of `natDegree_le_one_of_injective` (imports Mathlib only) | 0 errors |
| `MobiusGlue.lean` | §0 qm-pin definitions (verbatim); §1 rational functions; §2 named facts; §3 `mobiusGlue_of_curveFacts`; §4 `TwistClassFinite` from T5 and `AutOInnerFinite`; §5 `mobiusGlue_of_named`; §6 downstream (five qm-pin declarations verbatim, then `sameTripleMor_of_named`, `pointwise_of_witness_named`) | 0 errors, 0 warnings, about 6 s after `lake build ZInQKernel.HDecomp.QM.Leaves` (2m18s); 8 `#print axioms`, all `[propext, Classical.choice, Quot.sound]` |

**Integration.** The file imports only `ZInQKernel.HDecomp.QM.Leaves`.

- If qm-pin's full edit is adopted (`R1fpProps` with `R1famProps ∧ R1univProps`, plus the optional
  module `QM/Pin.lean`), then §1–§6 can be appended to `QM/Pin.lean`. Rename `R1fpPropsU` to the
  patched `R1fpProps`, and delete §0 and the five copied declarations of §6.
- §4 uses the kernel's `Level3.torsor`, `liftO`, `ofInt_sub`, `three_mul_ofInt` and
  `ObjBridge.TorsionStructure`, all from `QM/Structures.lean` and `Objects.lean`.
- New leaves for the decomposition's list: `CurveRatFactor`, `CurveSurj` (curve glue, textbook)
  and `AutOInnerFinite` (algebra, textbook). `TorsionStructure` is already T5.

## 5. What remains

- **The two curve facts.** They are true (§3.1, §3.2) and are the smallest point-level forms the
  argument needs.
  - A Lean proof needs curve theory that Mathlib v4.35 lacks: the degree of a finite morphism, the
    bijection between `P¹(ℚ̄)` and the points, and the factorization through the image curve.
  - A finer split is possible but was not pursued: "the image of `(σ, ρ)` is a plane curve",
    algebra on bivariate polynomials, and "two morphisms agreeing at cofinitely many points are
    equal". Each piece still needs the morphism property; §3.4 shows why a purely point-level
    argument cannot close the gap.
- **`AutOInnerFinite`.** STANDARD. A Lean proof would split into an extension of `α` to `B`,
  Skolem–Noether (proved in the kernel), and the normalizer computation for the maximal order of
  discriminant 6 (not attempted).
- **The CM objects** (`hCM`) come from the leaf bundle, as in qm-pin.
