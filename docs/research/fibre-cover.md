# fibre-cover: the glue Prop `FibreCoverExists` (G2: Proposition TS and Lemma NV)

Task fibre-cover, 2026-11-13. Object: `G0ModField.FibreCoverExists` from
`scratch/g0-mod-field/ModField.lean`, which g0-mod-field left open. Its statement and everything
it depends on (`IF`, `T`, `IsModelOver`, `FibreCtx`, `RationalFibre`, `FibreCoverOut`) are copied
verbatim into `scratch/fibre-cover/FibreCover.lean`, in the same namespace `G0ModField`. Nothing
upstream was edited. Log: `scratch/fibre-cover/log.md`. Compiler output:
`scratch/fibre-cover/compile_out.txt`. Model work only; no human review.

## 1. Main result

**`FibreCoverExists` is not refuted, and the relabeling of rv-g0pieces does not break it.**
The following is proved in Lean (VERIFIED: `lake env lean scratch/fibre-cover/FibreCover.lean`
gives 0 errors and 0 warnings; every `#print axioms` lists only `[propext, Classical.choice,
Quot.sound]`).

1. **G2's output depends only on the residue field of the point, from R1fp alone**
   (`fibreCoverOut_iff`). Take `(Y, Φ)` with `R1fpProps` and a `ℚ̄`-point `y` with
   `Φ y = [P]`. Then `FibreCoverOut Y Φ u P` holds if and only if
   `FibreFieldOut (residueImage y) u` holds. The latter says that `ℚ(y) ⊆ ℚ̄` lies in the
   splitting field of a separable `f ∈ ℚ[X]` of degree `≤ 324`, unramified outside `T(u)`.
   The rational fibre (`RationalFibre`: the `K`-point `y_K`, the object `PK/K`, and
   `PK.A ⊗ ℚ̄ ≅ P.A`) is proved for every `K ⊇ ℚ(y)` (`rationalFibre_of_le`). It uses the
   factorization of `y` through `K` (`exists_factor_of_residueImage_le`) and R1fp naturality.
   The model comes from the pullback square of `IsBaseChangeOf` (`isModelOver_of_baseChange`).
2. **The moduli bijection does not matter** (`fibreCoverOut_indep`). Let `Φ, Φ'` be two
   bijections on the same `Y`, both with R1fp, and let `y` be one point. Then G2's output for
   `(Φ, Φ y)` is equivalent to G2's output for `(Φ', Φ' y)`. Here is how this applies to a
   relabeled triple `(Y, Φ∘τ, π)` (rv-g0pieces `relabel`, with R1fp by `r1fp_relabel`). The
   point `y` over `J(u)` is the same, and only its object changes. So that triple satisfies G2 at
   `y` exactly when `(Y, Φ, π)` does.
3. **The reduction, compiled:**
   - `fibreCoverExists_of_twistClassCard : TwistClassCard → FibreUnramified → UnramifiedConjugates → FibreCoverExists`.
   - The corrected (pinned) form is `fibreCoverExists_of_pinned (Y₀ π₀) : TwistClassCard →
     CurvePinned Y₀ π₀ → FibreUnramifiedOn Y₀ π₀ → UnramifiedConjugates → FibreCoverExists`.
4. **The degree step needs no pin** (`fibreDegree_of : TwistClassCard → FibreDegree`). The
   bound `[ℚ(y):ℚ] ≤ 324` (with `ℚ(y)` finite over `ℚ`) follows, for every triple, from an
   intrinsic count of the `Aut 𝒪`-twist class of `P`. That count mentions no moduli scheme.

**What does break the universal form is not `Φ` but `(Y, π)`.** `FibreCtx` quantifies over every
`(Y, π)` that admits some `Φ` with R1fp and R2fp. Those clauses constrain `(Y, π)` only through
field points. The ramification step (Prop. TS) is a statement about the fibres of the genuine
cover `Y₃ → P¹`. Its proof from the leaves therefore needs `(Y, π)` pinned up to isomorphism
(`CurvePinned`, §3), which is weaker than pinning `Φ`. Once `(Y, π)` is pinned, the field part
and the ramification part follow as stated. These are the parts the task asked for: the
relabeling keeps them, and `fibreUnramified_of_pinned` proves the transfer.

## 2. The remaining Props

All of them are `def … : Prop` in `FibreCover.lean`, each with a docstring.

| Prop | kind | content | source | depends on the pin? |
|---|---|---|---|---|
| `TwistClassCard` | glue | the `Aut 𝒪`-twist class of a `QML3 ℚ̄` object has `≤ 324` isomorphism classes | N5 L425-441 (`≤ 4·|(𝒪/3𝒪)^*| ≤ 4·81`) | no (intrinsic) |
| `FibreUnramifiedOn Y₀ π₀` | glue | Prop. TS + Lemma NV on one curve: `ℚ(y)` is unramified outside `T(u)` for every `ℚ̄`-point `y` over `J(u)`, `u ∉ 𝒞` | N5 L484-529; h-decomposition G2 (inputs R1(d), R2, T1, T2) | no (one fixed curve) |
| `CurvePinned Y₀ π₀` | glue (after qm-pin) | every `(Y, π)` admitting `Φ` with R1fp, R2fp is isomorphic to `(Y₀, π₀)` over `P¹` on `ℚ̄`-points | rv-g0pieces §4, repair 1 | this *is* the pin |
| `UnramifiedConjugates` | textbook leaf | if `ℚ(α)` is unramified at `p`, so is the splitting field of `minpoly α` (a compositum of the conjugate fields) | Neukirch ANT I §9 / III §2 (UNVERIFIED locator), STANDARD | no |
| `FibreDegree` | glue, **proved** from `TwistClassCard` | `ℚ(y)` is finite with `[ℚ(y):ℚ] ≤ 324` | N5 L524-526 | no |
| `FibreUnramified` | glue, **proved** from `CurvePinned` + `FibreUnramifiedOn` | the universal form of Prop. TS | N5 L509-529 | yes |

### 2.1 Proof plan for `TwistClassCard` (not compiled)

This is a decomposition into smaller items, labelled as follows.

- *Classes.* A class in the twist class of `P = (A, ι, η)` has the form `[(A, ι∘α, η')]`, where
  `α ∈ Aut 𝒪` and `η'` is a level structure for `(A, ι∘α)`. This is glue: transport a level
  structure along the given QM isomorphism.
- *Inner twists.* For `u ∈ 𝒪^×`, the map `ι(u)` is an isomorphism `(A, ι∘Ad u) ≅ (A, ι)`. So
  only `Aut 𝒪 / Inn(𝒪^×) = N_B(𝒪)/ℚ^×𝒪^×` matters. That quotient is `(ℤ/2)²` for the maximal
  order of discriminant 6 (Atkin–Lehner `W`; Skolem–Noether, which is T13 and proved). This is
  glue: a computation on N5's `𝒪`.
- *Level structures.* By `Level3.linear`, `η'(a) = a·η'(1)`, and `3·η'(1) = η'(3) = 0`. So `η'`
  is determined by `η'(1) ∈ A[3]`. The textbook fact `|A[3]| = 3^{2·dim A} = 81` (Mumford §4,
  UNVERIFIED locator) then gives at most 81 choices. Glazer's bound `4·81 = 324` is the product.
  The sharper count is `|(𝒪/3𝒪)^×| = |GL₂(𝔽₃)| = 48`.

### 2.2 `FibreUnramifiedOn` (Prop. TS + Lemma NV)

This is the arithmetic core of G2, unchanged from h-decomposition. The chain is:

1. `Y₃ → P¹` has a smooth proper model over `ℤ[1/30]` (Buzzard Thm 2.1, Cor 2.3, N5 L443).
2. It is branched only over `0, ∞, −16/27`, tamely.
3. The pullback by `J` has indices `2, 6, 2`, which normalize to `2, 1, 1` (N5 L512-519).
4. The fibre over `u` is then unramified at `p ∉ T(u)` (T1 purity, T2 Abhyankar, or Beckmann
   1991 Prop. 4.2).

Already proved:

- the valuation case analysis (`GlueRepo.PR.inertia_orders_eq_one_iff`);
- `G⁶ − 97200F² = H²` and `J(u)` is not a branch value (`PkgI1`);
- Lemma NV step 2 (`LeafQM.AV.residue_unramified_over_branch`).

Two facts make this Prop the right target for that proof:

- **It mentions no moduli bijection.** `FibreUnramifiedOn Y₀ π₀` is about one curve and one map,
  so it can be proved on the genuine `(Y₃, π)` supplied by the leaves (`R1R2fp` with the
  good-reduction clause).
- **It is invariant under isomorphisms of curves.** `residueImage_comp_iso` shows that residue
  fields do not change along an isomorphism.

## 3. The pinning analysis

### 3.1 Why `Φ` does not matter

`FibreCoverOut Y Φ u P` concerns the fibre field `K`, the rational fibre and its model. The
rational fibre exists over any `K ⊇ ℚ(y)` by R1fp naturality. Conversely, a rational fibre over
`K` forces `y` to factor through `K`, because `Φ_{ℚ̄}` is injective. So the output is equivalent to
a property of `ℚ(y) = residueImage y` (`fibreCoverOut_iff`). This field is defined from the
scheme `Y` and the morphism `y`, and `Φ` does not enter it. The relabeling `τ` of rv-g0pieces
keeps `(Y, π, y)` and changes only the object `Φ(τ y)`, which may lie over another rational value
`s`. Hence it changes nothing (`fibreCoverOut_indep`; VERIFIED).

### 3.2 Why `(Y, π)` is not pinned by R1fp and R2fp

This is an argument, not compiled.

- **`Y` is pinned up to isomorphism (SPECULATIVE).** Take `Ψ = Φ₀⁻¹ ∘ Φ : Y(K) ≃ Y₀(K)`, which
  is natural in all fields `K`, including function fields. Naturality preserves "factors through
  a subfield algebraic over `ℚ`". So `Ψ` maps the generic point to the generic point. Then
  naturality at `K = ℚ(Y)` and at `K = ℚ(Y₀)` gives mutually inverse field maps
  `ℚ(Y₀) ⇄ ℚ(Y)`. Smooth proper curves that are birational are isomorphic. So `Y ≅ Y₀`, but the
  isomorphism need not agree with `Ψ` on closed points.
- **`π` is not pinned.** Transport `π` along `Y ≅ Y₀`. The result is a morphism `π' : Y₀ → P¹`
  of degree `N = deg π₀`. Its `ℚ̄`-fibres are `ρ⁻¹` of the fibres of `π₀`, for some bijection `ρ`
  of closed points that is Galois-equivariant and preserves residue fields. So `π'` is again a
  cover branched only over `0, ∞, −16/27`, with the same fibre cardinalities. Two cases:
  - If `π' = π₀ ∘ a` for an automorphism `a`, then `CurvePinned` holds.
  - Otherwise `π'` is a second Belyi-type map on `Y₀` whose fibre partition matches that of `π₀`
    under such a `ρ`. Ramification indices within a fibre could then differ from those of `π₀`.
    In that case the inertia orders of the specialization at `J(u)` could differ, and `T(u)`
    could be insufficient.
- **Status.** Whether such a `π'` exists is open here: it was neither found nor excluded. So
  `FibreUnramified`, as stated, is not provable from the existentially stated leaves without
  `CurvePinned`. Verdict: **UNSURE as stated, TRUE for the genuine `(Y₃, π)`**. This matches
  rv-g0pieces' verdict on the other three pieces, but for a different reason.

### 3.3 After the repair

qm-pin's repair 1 makes `Φ` induced by a universal family. Then `CurvePinned` becomes glue, by
the following argument (UNVERIFIED as Lean, STANDARD as mathematics):

1. Yoneda for the fine moduli scheme gives `g : Y ≅ Y₀` with `Φ = Φ₀ ∘ g`.
2. `π ∘ g⁻¹` is constant on the fibres of the Galois quotient `π₀ : Y₀ → Y₀/G ≅ P¹` (N5 L436),
   so it factors through a morphism `h : P¹ → P¹`.
3. `h` is bijective on `ℚ̄`-points, so in characteristic 0 it is a Möbius map.
4. `h` fixes `0, ∞, −16/27`, so `h = id`.

Because of `fibreCoverOut_indep`, G2 needs only this pin of `(Y, π)`, not the full pin of `Φ`.

## 4. Lean outcomes (`scratch/fibre-cover/FibreCover.lean`, 460 lines)

All results below are proved without `sorry`, with standard axioms, and are VERIFIED.

- **Verbatim copies.** `IF`, `T`, `IsModelOver`, `FibreCtx`, `RationalFibre`, `FibreCoverOut`,
  `FibreCoverExists`.
- **Part 1.**
  - Points and residue fields: `spec_to_specQ_eq` (copied from rv-g0pieces),
    `exists_factor_of_residueImage_le`, `residueImage_le_aux`, `residueImage_comp_le`.
  - The rational fibre: `isModelOver_of_baseChange`, `rationalFibre_of_le`.
  - The reduction to the residue field: `FibreFieldOut` (def), `fibreCoverOut_iff`,
    `fibreCoverOut_indep`.
- **Part 2.** `UnramifiedConjugates` (def) and `fibreFieldOut_of`: a primitive element `β`
  gives `f = minpoly β`, which is separable of degree `[F:ℚ]`.
- **Part 3.** `FibreDegree` and `FibreUnramified` (defs), and `fibreCoverExists_of`.
- **Part 4.** `TwistClassCard` (def) and three theorems:
  - `finrank_le_of_card_algHom_le`: uses `AlgHom.card` and
    `IsAlgClosed.surjective_domRestrict_of_isAlgebraic`.
  - `finiteDimensional_of_card_algHom_le`: if a subfield of `ℚ̄` has at most `n` embeddings into
    `ℚ̄`, it is finite of degree `≤ n`. The proof takes a maximal finite subfield via
    `Nat.findGreatest`.
  - `fibreDegree_of`.
- **Part 5.**
  - Residue fields along morphisms: `residueImage_comp_le_self(_aux)`, `residueImage_comp_iso`.
  - The pin: `FibreUnramifiedOn`, `CurvePinned` (defs), `fibreUnramified_of_pinned`.
  - The composites: `fibreCoverExists_of_twistClassCard`, `fibreCoverExists_of_pinned`.

**Imports.** `ZInQKernel.HDecomp.QM.Leaves`, `HDecomp.Descent.Constants`,
`HDecomp.Descent.B2Glue`, `Multiplication.Certificate.Constants` and `Hypotheses.JHeight`. Build
`ZInQKernel.HDecomp.QM.Leaves` first (4 min). After that, `lake env lean` takes about 2 min.

**Integration.** The names agree with `ModField.lean`, so the file can be appended there (drop
the copied definitions). `fieldDescent` and `modularConstituent_of_ranges` then take
`TwistClassCard`, `CurvePinned Y₀ π₀`, `FibreUnramifiedOn Y₀ π₀` and `UnramifiedConjugates` in
place of `FibreCoverExists`.

## 5. What remains

- `FibreUnramifiedOn` on the genuine curve: Prop. TS from T1-T2 or Beckmann. This needs integral
  models of `Y₃ → P¹` and function-field Galois theory, which are not in Mathlib v4.35; it is the
  large item of h-decomposition G2.
- `TwistClassCard`: the three items of §2.1.
- `CurvePinned`: depends on qm-pin.
- `UnramifiedConjugates`: textbook; not in Mathlib v4.35 for `UnramifiedAt`.
