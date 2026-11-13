# mobius-glue: the `π`-half of qm-pin's comparison, reduced to named facts

Task mobius-glue, 2026-11-13. Base 2dd83306 merged with `origin/wip/qm-pin`. Scratch:
`scratch/mobius-glue/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or another
task's directory was edited. Model work only, no human review.

## 1. Result

**`MobiusGlue` is proved in Lean from two named curve facts and one existing textbook leaf**
(`scratch/mobius-glue/MobiusGlue.lean`; compiled, 0 errors, 0 warnings; axioms
`[propext, Classical.choice, Quot.sound]`; VERIFIED):

```lean
theorem mobiusGlue_of_curves (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue
```

| name | kind | content | status |
|---|---|---|---|
| `CurveRatFactor` | curves | on a proper smooth curve `S/ℚ`, if `ρ : S → P¹` is constant on the fibres of `σ : S → P¹` (on `ℚ̄`-points), then `ρ = R ∘ σ` at every `ℚ̄`-point with finite `σ`-value, for a rational function `R = [F : G]`, `F, G ∈ ℚ̄[t]` coprime | STANDARD (§3.1); not in Mathlib |
| `CurveSurj` | curves | a morphism `S → P¹` from a proper smooth curve over `ℚ` with a `ℚ̄`-point, whose fibres on `ℚ̄`-points are finite, is onto `P¹(ℚ̄)` | STANDARD (§3.2); not in Mathlib |
| `ObjBridge.TorsionStructure` | textbook leaf T5 | `A(K̄)[n] ≅ (ℤ/n)^{2g}` (Mumford §4) | already in `TextbookLeaves` (h-decomposition T5) |

`MobiusGlue` is copied verbatim from `scratch/qm-pin/QMPin.lean`, together with the qm-pin
definitions it uses (`QMFamily`, `IsFibreOf`, `R1famProps`, `R1fpPropsPin`, `R1univProps`,
`R1fpPropsU`). A Python string comparison confirmed that each declaration's text is identical
(VERIFIED).

The downstream consumers follow from the same three inputs (compiled):

- `sameTripleMor_of_curves`: two triples satisfying the fully repaired list are `SameTripleMor`;
- `pointwise_of_witness_curves`: a fibre statement proved for the leaf's own triple holds for every
  triple. This is the form used by `FibreSimple`, `ThetaPointOfFibre` and `ModularConstituent`.

The CM-object hypothesis `hCM` stays as in qm-pin. It follows from the leaf bundle
(`cm_objects_of_R1R2fp`, qm-pin).

**What is proved, not assumed.** All of the following is compiled.

1. **A Möbius map fixing `0, ∞, c` is the identity.**
   - `Mob.natDegree_le_one_of_injective`: over an algebraically closed field of characteristic 0,
     if `F, G` are coprime and `t ↦ [F(t) : G(t)]` is injective on `K`, then `deg F, deg G ≤ 1`.
     The proof uses the Wronskian `F'G − FG'`: it is nonzero, and for all but at most one `c`, the
     unique root of `F − cG` is a root of the Wronskian.
   - `Mob.ratEval_eq_self`: such a function with no finite pole, fixing `0` and some `c ≠ 0`, is
     the identity.
2. **The reduction `mobiusGlue_of_curveFacts`.** It derives `MobiusGlue` from `CurveRatFactor`,
   `CurveSurj` and `TwistClassFinite` (a twist class contains only finitely many isomorphism
   classes). The steps:
   - `π'` and `π ∘ g` have the same fibres;
   - the CM points exist on `Y'`, because `Φ'` is onto;
   - the fibres of `π ∘ g` are finite, so `π ∘ g` is onto `P¹(ℚ̄)`, and the factor `R` is injective;
   - `R` has no finite pole (look at the fibre over `∞`) and fixes `0` and `−16/27`;
   - so `R = id`, and `π' = π ∘ g` on `ℚ̄`-points.
3. **`TwistClassFinite` from T5 alone** (`twistClassFinite`).
   - `level3_finite`: in characteristic 0, a pair `(A, ι)` carries only finitely many level
     structures. The proof goes through the kernel's `Level3.torsor`: a level structure is
     `a ↦ η₀(a u₀)`, which depends only on `u₀ mod 3𝒪`.
   - `transportLevel` and `QML3.isoTransport` transport level structures along isomorphisms of QM
     pairs.
   - `conjUnitIso`: the twists by `t` and by `v t v⁻¹` are isomorphic through `ι(v)`.
   - `autOInnerFinite`: `Aut(𝒪)` modulo conjugation by `𝒪^×` is finite, proved in two steps:
     - (§7) An explicit extension of `α ∈ Aut 𝒪` to `α̃ ∈ Aut_ℚ(B)` (`extAlgEquiv`, with
       `α̃(b) = m⁻¹ α(m b)`). Skolem–Noether, proved in the kernel
       (`TSkolemKW.leafSkolemNoether`, through `GlueDescent.B6_inner`), makes `α̃` inner by some
       `u ∈ B^×` normalizing `𝒪`.
     - (§8) **`NormalizerFinite`, proved**: every `u ∈ B^×` normalizing `𝒪` is `q · v · t` with
       `q ∈ ℚ^×`, `v ∈ 𝒪^×` and `t ∈ {1, i, j, ij}`. The proof is a descent on `|nrd u|`, after
       scaling `u` into `𝒪`:
       - a prime `p ∤ 6` dividing `nrd u` divides `u`, by the identity
         `6 x_l² = Σ λ · coord(u e_k ū)` (integer coefficients from PARI's `matsolvemod`), because
         `u e_k ū ∈ nrd(u) 𝒪`;
       - `2 | nrd u` gives `u i⁻¹ ∈ 𝒪`, and `3 | nrd u` gives `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by
         `decide`);
       - `{1, i, j, ij}` is closed under right multiplication by `i` and `j` up to `ℚ^×`.

**Hypotheses of `MobiusGlue` the proof uses:**

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

`NormalizerFinite` (§7, proved in §8) reads: `∃ T : Set Bˣ, T.Finite ∧ ∀ u : Bˣ,
(∀ a, a ∈ O ↔ u a u⁻¹ ∈ O) → ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ u = algebraMap q * v * t`.

`Mob.ratEval F G t` is `∞` if `G(t) = 0` and `F(t)/G(t)` otherwise: the value of `[F : G]` at a
finite point. The ingredients are all genuine definitions:

- the kernel's `ToP1` (a morphism to `P¹` by charts) and `ToP1.val` (its value at a field point,
  through Mathlib's `Scheme.SpecToEquivOfField`);
- `fieldPt`, `QML3`, `M3`, `QMIso` and `QMStr.twist` from `ZInQKernel/HDecomp/QM/`;
- Mathlib's `Polynomial`, `IsCoprime`, `IsProper` and `SmoothOfRelativeDimension`.

None of the named facts quantifies over an invented structure.

## 3. Why the named facts are true (argued; not compiled)

**Independent check.** A fresh model agent, not anchored on this report, reviewed both curve facts
against the definitions. It was given only the Lean statements and the kernel's `ToP1`, and asked
for counterexamples. It found both TRUE. (This was a model review, not a human one.)

- It confirmed that `ToP1` glues to a genuine morphism to `P¹_ℤ` and that `ToP1.val` is the usual
  value.
- It confirmed that coprime pairs `(F, G)` represent exactly the morphisms `P¹ → P¹`, constants and
  `∞` included.
- It confirmed that the edge cases are covered: components defined over a number field, `σ` or `ρ`
  identically `∞`, and `ρ = ∞` over finite values.
- It showed that properness is necessary for `CurveRatFactor`. Take `S = (𝔸¹ ∖ {0}) ⊔ pt`, with
  `σ = ρ = id` on the first piece and `σ = 0`, `ρ = 1` on the point. The fibre condition holds, but
  no rational `R` fits.
- Smoothness and relative dimension 1 matter only for `CurveSurj`, where they make "finite fibres"
  imply "nonconstant on every component".

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

### 3.3 `AutOInnerFinite` (now proved, §1 item 3)

The argument is the standard one: Skolem–Noether, then the normalizer of a maximal order,
`N(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²` for discriminant 6, generated by `i` and `j`. It is now compiled.

- Skolem–Noether comes from the kernel's proof.
- The normalizer step is an elementary descent, made concrete by three computations:
  - the identity `6 x_l² = Σ λ · coord(u e_k ū)` (the Smith form of the 16 quadratic forms
    `coord_l(u e_k ū)` on the 10 monomials is `diag(1,1,1,1,1,6,6,6,6,6)`;
    `scratch/mobius-glue/py/normalizer_identity.py`, VERIFIED);
  - the residue checks modulo 2 and 3.

### 3.4 Why some finiteness is needed

The finite-fibre input cannot be dropped. Suppose `π'` were constant on every geometric component
of `Y'`. Then the image of `π'` is finite, and `h` (with `π' = h ∘ π ∘ g`) is only some bijection
of that finite set fixing `0, ∞, −16/27`. No point-level argument excludes this.

Over the kernel's definitions, the fibre of `π'` through `y` is in bijection, via `Φ'`, with a
twist class. So `TwistClassFinite` is the natural form. Its proof needs both of the following:

- finitely many level structures per pair (`TorsionStructure`);
- finitely many pair classes per twist class (`AutOInnerFinite`, now proved).

The second is necessary: if `End(A) = ι(𝒪)`, the pair classes `(A, ι ∘ α)` correspond exactly to
`Aut(𝒪)` modulo inner automorphisms by units.

## 4. Lean outcomes (all VERIFIED; logs in `scratch/mobius-glue/log.md`)

| file | content | outcome |
|---|---|---|
| `MobiusGlue.lean` (the deliverable) | §0–§8 as in its header | 0 errors, 0 warnings; 16 `#print axioms`, all `[propext, Classical.choice, Quot.sound]` (`run_final.txt`) |
| `RatInj.lean` | development copy of §1 (imports Mathlib only) | 0 errors |
| `AutO.lean` | development copy of §7 | 0 errors |
| `Normalizer.lean` | development copy of §8 | 0 errors |
| `py/normalizer_identity.py` | `mulCoord` check, norm and conjugate formulas, Smith form, PARI coefficients, residue checks modulo 2 and 3 | all checks pass |

**Build prerequisites.**

- Run `lake build ZInQKernel.HDecomp.QM.Leaves` (2m18s) and
  `lake build ZInQKernel.HDecomp.Textbook.SkolemNoether` (51 s) first.
- After that, `lake env lean scratch/mobius-glue/MobiusGlue.lean` runs in under a minute.

**Integration.** The file imports `ZInQKernel.HDecomp.QM.Leaves` and
`ZInQKernel.HDecomp.Textbook.SkolemNoether`.

- **If qm-pin's full edit is adopted** (`R1fpProps` with `R1famProps ∧ R1univProps`, plus the
  optional module `QM/Pin.lean`):
  - §1–§8 can go into a new module after `QM/Pin.lean`;
  - rename `R1fpPropsU` to the patched `R1fpProps`;
  - delete §0 and the five copied declarations of §6.
- §4 uses the kernel's `Level3.torsor`, `liftO`, `ofInt_sub`, `three_mul_ofInt`, `ofInt_injective`
  and `ObjBridge.TorsionStructure`. §7 uses `GlueDescent.B6_inner` and
  `TSkolemKW.leafSkolemNoether`.
- **New leaves for the decomposition's list:** `CurveRatFactor` and `CurveSurj` (curve glue,
  textbook). `TorsionStructure` is already T5.

## 5. What remains

- **The two curve facts.** They are true (§3.1, §3.2) and are the smallest point-level forms the
  argument needs.
  - A Lean proof needs curve theory that Mathlib v4.35 lacks: the degree of a finite morphism, the
    bijection between `P¹(ℚ̄)` and the points, and the factorization through the image curve.
  - A finer split is possible: "the image of `(σ, ρ)` is a plane curve", algebra on bivariate
    polynomials, and "two morphisms agreeing at cofinitely many points are equal". Each piece still
    needs the morphism property; §3.4 shows that a purely point-level argument cannot close the gap.
- **The CM objects** (`hCM`) come from the leaf bundle, as in qm-pin.
