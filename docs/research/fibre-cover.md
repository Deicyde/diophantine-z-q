# fibre-cover: the glue Prop `FibreCoverExists` (G2: Proposition TS and Lemma NV)

Task fibre-cover, 2026-11-13. Object: `G0ModField.FibreCoverExists` from
`scratch/g0-mod-field/ModField.lean`, which g0-mod-field left open. Its statement and everything
it depends on (`IF`, `T`, `IsModelOver`, `FibreCtx`, `RationalFibre`, `FibreCoverOut`) are copied
into `scratch/fibre-cover/FibreCover.lean` in the same namespace `G0ModField`. A script checked
that the copies are character-identical to the originals (VERIFIED). Nothing upstream was edited.
Log: `scratch/fibre-cover/log.md`. Compiler output: `scratch/fibre-cover/compile_out.txt`.
Model work only; no human review.

## 1. Main result

**`FibreCoverExists` is not refuted, and the relabeling of rv-g0pieces does not break it.**
It is reduced in Lean to strictly smaller named Props, two of which are already proved.
VERIFIED: `lake env lean scratch/fibre-cover/FibreCover.lean` gives 0 errors and 0 warnings;
all 14 `#print axioms` lines list only `[propext, Classical.choice, Quot.sound]`.

**Pinned form.**

```
fibreCoverExists_of_propTS (Y₀ π₀) :
  PkgI2.TorsionStructure.{0}      -- textbook leaf T5 of the bundle (Mumford §4)
  → InnerTwistCount               -- glue: |N_B(𝒪)/ℚ^×𝒪^×| ≤ 4
  → CurvePinned Y₀ π₀             -- glue (pin of (Y, π) up to iso; qm-pin)
  → PropTS Y₀ π₀                  -- glue from leaves: Prop. TS (Beckmann / T1-T2 + R1(d))
  → UnramifiedConjugates          -- textbook: Galois closure of an unramified field
  → FibreCoverExists
```

**Pin-free form.**

```
fibreCoverExists_of_propTSAll :
  PkgI2.TorsionStructure.{0} → InnerTwistCount → PropTSAll → UnramifiedConjugates → FibreCoverExists
```

What is proved on the way:

1. **G2's output depends only on the residue field of the point, from R1fp alone**
   (`fibreCoverOut_iff`). Take `(Y, Φ)` with R1fp and a `ℚ̄`-point `y` with `Φ y = [P]`. Then
   `FibreCoverOut Y Φ u P` is equivalent to the field part: `ℚ(y) = residueImage y` lies in the
   splitting field of a separable `f ∈ ℚ[X]` of degree `≤ 324`, unramified outside `T(u)`.
   - The rational fibre is proved over every `K ⊇ ℚ(y)` (`rationalFibre_of_le`). It consists of
     the `K`-point `y_K`, the object `PK/K`, and the model `PK.A ⊗ ℚ̄ ≅ P.A`.
   - The ingredients are the factorization `y = y_K ∘ Spec(K ⊆ ℚ̄)`
     (`exists_factor_of_residueImage_le`), R1fp naturality, and the pullback square of
     `IsBaseChangeOf` (`isModelOver_of_baseChange`).
2. **The moduli bijection does not matter** (`fibreCoverOut_indep`). Let `Φ, Φ'` be two
   bijections on the same `Y`, both with R1fp, and let `y` be one point. Then G2 holds for
   `(Φ, Φ y)` if and only if it holds for `(Φ', Φ' y)`. A relabeled triple `(Y, Φ∘τ, π)` keeps
   `(Y, π, y)` and changes only the object. So it satisfies G2 exactly when `(Y, Φ, π)` does.
3. **The degree bound needs no pin.** `fibreDegree_of : TwistClassCard → FibreDegree`. The
   embeddings `e` of `ℚ(y)` give distinct points `e∘y_F` over `J(u)`, and R2fp puts their classes
   into the `Aut 𝒪`-twist class of `P`. A subfield of `ℚ̄` with at most `n` embeddings into `ℚ̄` is
   finite of degree `≤ n` (`finiteDimensional_of_card_algHom_le`).
4. **Glazer's `4·81` count.** `twistClassCard_of : TorsionBound3 → InnerTwistCount → TwistClassCard`.
   A class in the twist class is `[(A, ι∘w, η')]` with `w` among at most 4 twists, and `η'` is
   determined by the 3-torsion point `η'(1)`.
   - The Lean steps are `innerIso`, `transportLevel`, `transportIso`, `level3_ext` and
     `level3_three`.
   - `torsionBound3_of_t5 : PkgI2.TorsionStructure.{0} → TorsionBound3`: the map
     `A(ℚ̄)[3] ↪ A(AlgebraicClosure ℚ̄)[3] ≃ (ℤ/3)⁴` shows `|A(ℚ̄)[3]| ≤ 81`.
5. **The valuation half of Prop. TS is the repository's.** `fibreUnramifiedOn_of_propTS`: for
   `p ∉ T(u)` we have `p > 324` and `p ∤ M_S(u)`. So the three Beckmann inertia orders at
   `t = J(u)` are 1, by `GlueRepo.PR.inertia_trivial_iff_not_dvd`.
6. **Only `(Y, π)` needs pinning, and only up to isomorphism.** `fibreUnramified_of_pinned` uses
   `residueImage_comp_iso`.

**Where the universal statement is weak.** `FibreCtx` quantifies over every `(Y, π)` that admits
some `Φ` with R1fp and R2fp. These clauses constrain `(Y, π)` only through field points. So the
ramification step needs either the pin `CurvePinned`, or Prop. TS for every such cover
(`PropTSAll`). Both are argued true in §3, but neither follows from the existentially stated
leaves without further glue. The field part and the ramification part, which the task asked for,
are proved under either: on the pinned curve, they are `fibreUnramified_of_pinned` with
`fibreUnramifiedOn_of_propTS`.

## 2. The named Props

All are `def … : Prop` in `FibreCover.lean`, each with a docstring.

| Prop | kind | content | source | status |
|---|---|---|---|---|
| `PkgI2.TorsionStructure.{0}` | textbook leaf (bundle T5) | `A(K̄)[n] ≅ (ℤ/n)^{2g}` | Mumford §4 | leaf, in `TextbookLeaves.t5` |
| `InnerTwistCount` | glue (a computation on N5's `𝒪`) | every `α ∈ Aut 𝒪` is `w ∘ Ad u`, with `w` in a fixed set of `≤ 4` and `u ∈ 𝒪^×` | `Aut 𝒪 = N_B(𝒪)/ℚ^×` (Skolem–Noether T13, proved); `N_B(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²` (Atkin–Lehner; N5 L425-429; Vignéras, UNVERIFIED locator) | open |
| `PropTS Y₀ π₀` | glue from leaves | rational non-branch `t`, `p > 324`, inertia orders `4/(4,v_p(t)⁺)`, `6/(6,(−v_p t)⁺)`, `2/(2,v_p(t+16/27)⁺)` all 1 ⇒ `ℚ(y)` unramified at `p` for `y` over `t` | N5 L484-525; Beckmann 1991 Prop. 4.2 (UNVERIFIED number) or T1-T2; R1(d) (Buzzard's model over `ℤ[1/30]`); indices `4, 6, 2` | open: the large item of h-decomposition G2 |
| `CurvePinned Y₀ π₀` | glue | every `(Y, π)` admitting `Φ` with R1fp, R2fp is isomorphic to `(Y₀, π₀)` over `P¹` on `ℚ̄`-points | rv-g0pieces §4 repair 1; §3 below | open (qm-pin) |
| `PropTSAll` | glue | `PropTS Y π` for every admissible `(Y, π)` | §3.2 | open; alternative to `CurvePinned` |
| `UnramifiedConjugates` | textbook | if `ℚ(α)` is unramified at `p`, so is the splitting field of `minpoly α` | compositum of unramified fields (Neukirch ANT I §9/III §2, UNVERIFIED locator) | open, not in Mathlib v4.35 for `UnramifiedAt` |
| `TorsionBound3` | glue | `A(ℚ̄)[3]` has `≤ 81` points, `dim A = 2` | — | **proved** from T5 |
| `TwistClassCard` | glue | the twist class of a `QML3 ℚ̄` object has `≤ 324` classes | N5 L436-441 | **proved** from `TorsionBound3`, `InnerTwistCount` |
| `FibreDegree` | glue | `ℚ(y)` finite, `[ℚ(y):ℚ] ≤ 324` | N5 L524-526 | **proved** from `TwistClassCard` |
| `FibreUnramifiedOn`, `FibreUnramified` | glue | `ℚ(y)` unramified outside `T(u)` (one curve; every admissible curve) | N5 L509-529 | **proved** from `PropTS` (+ `CurvePinned`) or from `PropTSAll` |

## 3. The pinning analysis

### 3.1 `Φ` does not matter (VERIFIED)

`FibreCoverOut` is equivalent to a property of `ℚ(y)` (`fibreCoverOut_iff`). This field is
defined from the scheme `Y` and the morphism `y`; `Φ` does not enter it. The relabeling `τ` keeps
`(Y, π, y)`. The object `Φ(τy)` may lie over another rational value `s`, but that changes nothing
(`fibreCoverOut_indep`).

### 3.2 `(Y, π)` is not pinned by the clauses

The arguments in this subsection are not compiled.

- **`Y` (SPECULATIVE).** Take `Ψ = Φ₀⁻¹ ∘ Φ : Y(K) ≃ Y₀(K)`, natural in all fields `K`,
  including function fields.
  - Naturality preserves "factors through a subfield algebraic over `ℚ`". So `Ψ` maps the generic
    point to the generic point.
  - Naturality at `ℚ(Y)` and at `ℚ(Y₀)` gives mutually inverse field maps.
  - Smooth proper curves that are birational are isomorphic, so `Y ≅ Y₀`. The isomorphism need
    not agree with `Ψ` on closed points.
- **`π` (SPECULATIVE, likely true).** R2fp gives three facts about `π`:
  - its `ℚ̄`-fibres are `Ψ⁻¹` of the fibres of `π₀`;
  - `Ψ` is Galois-equivariant and preserves residue fields;
  - CM points go to `0, ∞, −16/27`.

  Hence every rational fibre of `π` is isomorphic, as a Galois set with residue fields, to a
  rational fibre of `π₀`. Off the branch values these are `G`-torsors, because `G` acts over `ℚ`
  (R1hecke). The argument then runs:
  1. Take a rational `t` given by Hilbert irreducibility for `π`. The Galois image on
     `π⁻¹(t)` is the full arithmetic monodromy `M` of `π`.
  2. That image lies in the centralizer of a regular action, so `M` is regular and
     `|M| = deg π = |G|`.
  3. So `π` is Galois, branched only over `0, ∞, −16/27`, with the same fibre cardinalities and
     hence the same indices `4, 6, 2`.
  4. Beckmann's theorem then gives `PropTS Y π` with the same inertia orders (`PropTSAll`).

  Alternatively, if `Aut(Y₃ ⊗ ℚ̄) = G` (expected from the maximality of the triangle group
  `(2,4,6)`; Singerman 1972, UNVERIFIED), then `π = π₀ ∘ g` (`CurvePinned`).
- **Status.** As stated, `FibreCoverExists` is true if these arguments are right, i.e. likely
  TRUE. It is not provable from the existential leaves without one of the two glue Props. Both
  need Hilbert irreducibility or automorphism groups of curves, which Lean lacks today.

### 3.3 After the repair

qm-pin's repair 1 makes `Φ` induced by a universal family. `CurvePinned` then becomes light glue,
by the following argument (UNVERIFIED as Lean, STANDARD as mathematics):

1. Yoneda for the fine moduli scheme gives `g : Y ≅ Y₀`.
2. `π ∘ g⁻¹` is constant on the fibres of the Galois quotient `π₀`, so it factors through a
   morphism `h : P¹ → P¹`.
3. `h` is bijective on `ℚ̄`-points, so in characteristic 0 it is a Möbius map.
4. `h` fixes `0, ∞, −16/27`, so `h = id`.

Because of `fibreCoverOut_indep`, G2 needs only this pin of `(Y, π)`.

## 4. Lean outcomes (`scratch/fibre-cover/FibreCover.lean`, 745 lines)

Every theorem below is proved without `sorry`, with standard axioms, and is VERIFIED.

- **Part 1, the residue field.**
  - Points and residue fields: `spec_to_specQ_eq`, `exists_factor_of_residueImage_le`,
    `residueImage_le_aux`, `residueImage_comp_le`.
  - The rational fibre: `isModelOver_of_baseChange`, `rationalFibre_of_le`.
  - The reduction: `FibreFieldOut` (def), `fibreCoverOut_iff`, `fibreCoverOut_indep`.
- **Part 2.** `UnramifiedConjugates` (def) and `fibreFieldOut_of`: a primitive element `β`
  gives `f = minpoly ℚ β`.
- **Part 3.** `FibreDegree`, `FibreUnramified` (defs) and `fibreCoverExists_of`.
- **Part 4.** `TwistClassCard` (def), `finrank_le_of_card_algHom_le`,
  `finiteDimensional_of_card_algHom_le`, `fibreDegree_of`.
- **Part 5.**
  - Residue fields along morphisms: `residueImage_comp_le_self(_aux)`, `residueImage_comp_iso`.
  - The pin: `FibreUnramifiedOn`, `CurvePinned` (defs), `fibreUnramified_of_pinned`.
  - Composites: `fibreCoverExists_of_twistClassCard`, `fibreCoverExists_of_pinned`.
- **Part 6.**
  - Defs: `TorsionBound3`, `InnerTwistCount`.
  - Level structures: `level3_eta_eq`, `level3_ext`, `level3_three`.
  - Isomorphisms: `innerIso`, `transportLevel`, `transportIso`.
  - Composites: `twistClassCard_of`, `fibreCoverExists_of_pinned'`.
- **Part 7.** `spec_comp_injective`, `specIncl`, `torsionBound3_of`, `torsionBound3_of_t5`,
  `fibreCoverExists_of_leafTorsion`.
- **Part 8.**
  - Defs: `PropTS`, `PropTSAll`.
  - Theorems: `fibreUnramifiedOn_of_propTS`, `fibreCoverExists_of_propTS`,
    `fibreUnramified_of_propTSAll`, `fibreCoverExists_of_propTSAll`.

**Imports.** `ZInQKernel.HDecomp.QM.Leaves`, `HDecomp.Descent.Constants`,
`HDecomp.Descent.B2Glue`, `HDecomp.Repo.PRArith`, `Multiplication.Certificate.Constants` and
`Hypotheses.JHeight`. Build `ZInQKernel.HDecomp.QM.Leaves` first (4 min). After that,
`lake env lean` takes about 2 min.

**Lean pitfalls.**
- Under `open MonObj`, the names `ι` and `η` are tokens, and `mul_one`, `mul_assoc`, `one_mul`
  resolve to MonObj lemmas; write `_root_.mul_one` and so on.
- Rewriting with `(fieldMap e ≫ y).left = Spec.map … ≫ y.left` produces ill-typed motives
  (`(fieldPt K).left` against `Spec (of K)`). State lemmas at the scheme level and apply them to
  `y.left`.

**Integration.** The names agree with `ModField.lean`, so the file can be appended there (drop
the copied definitions). `fieldDescent` and `modularConstituent_of_ranges` then take the five
inputs of `fibreCoverExists_of_propTS` in place of `FibreCoverExists`.

## 5. What remains

- `PropTS` on the genuine `(Y₃, π)`: Beckmann, or T1-T2 with R1(d). This needs integral models
  of `Y₃ → P¹` and function-field Galois theory; it is the large G2 item of h-decomposition.
- `InnerTwistCount`: the normalizer of N5's `𝒪`.
- `CurvePinned` (from qm-pin) or `PropTSAll`.
- `UnramifiedConjugates`: textbook.
