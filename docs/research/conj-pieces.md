# conj-pieces: `ArtinTorsionSurj`, `HomLinearLift`, `ConjUniformization` (G10, under `ConjTwistNontrivial`)

Task conj-pieces, 2026-11-13. Lean: `scratch/conj-pieces/` (`Artin.lean`, `Holo.lean`,
`Conj.lean`, and the assembled `ConjPieces.lean`). Log: `scratch/conj-pieces/log.md`.
Check with `lake env lean scratch/conj-pieces/<file>.lean` after
`lake build ZInQKernel.HDecomp.LeafPush2.T`. None of the four files has a `sorry`. Every
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` (VERIFIED, compiled 2026-11-13;
`ConjPieces.lean` takes 35 s and has 35 `#print axioms`).

## Result

**All three of conj-twist's remaining Props are now reduced to leaves in Lean.**

- `ArtinTorsionSurj` (N1-surj) is **proved** from the existing leaf `MulIsogeny`.
- `HomLinearLift` (N2) is **proved** from a new, purely analytic textbook leaf `HoloHomLift`.
- `ConjUniformization` (N3a) is **reduced** to a smaller analytic glue Prop `ConjHolo`.
  - `ConjHolo` is **proved** whenever `s` is bijective.
  - So the number-field form `ConjUniformizationNF` is **proved outright**. conj-twist only ever
    uses N3a for number fields.

So `ConjTwistNontrivial` (G10's core) rests on leaves only. VERIFIED, compiled
(`ConjPieces.lean`):

```
G0Galois.conjTwistNontrivial_leaves :
  PkgI3.TateModuleFree → ZInQ.LeafPush2.UniformizationExists →
  G0FibreSimple.MulIsogeny → HoloHomLift → ConjTwistNontrivial

G0Galois.conjTwistFromLeaves_leaves :
  G0FibreSimple.MulIsogeny → HoloHomLift → ConjTwistFromLeaves
```

`PkgI3.FaltingsTate` is a hypothesis inside `ConjTwistNontrivial`. Leaf status of each:

- `TateModuleFree` (T26), `UniformizationExists` (T35) and `FaltingsTate` are leaves already in
  the build.
- `MulIsogeny` is already a LEAF of g0-assemble's `GluePieces2` (field 1, `mulIsogeny`).
- **The only new leaf is `HoloHomLift`.** It replaces conj-twist's new leaf `HomLinearLift`.
- The two glue Props `ArtinTorsionSurj` and `ConjUniformization` are no longer needed.

Proved per Prop:

| Prop (verbatim from `scratch/conj-twist/ConjTwist.lean`) | Result | Lean |
|---|---|---|
| `ArtinTorsionSurj` | **proved from the leaf `MulIsogeny`** | `artinTorsionSurj_of_mulIsogeny` (`Artin.lean`) |
| `HomLinearLift` | **proved from the new textbook leaf `HoloHomLift`** | `homLinearLift_of_holoHomLift` (`Holo.lean`) |
| `ConjUniformization` | **reduced to the glue `ConjHolo`**; ConjHolo proved for bijective `s`; `ConjUniformizationNF` (the `[NumberField K]` form) proved outright | `conjUniformization_of_conjHolo`, `conjHolo_of_bijective`, `conjUniformizationNF` (`Conj.lean`) |

No statement was changed.

- The three Props are copied verbatim, together with what they depend on: 20 blocks of
  conj-twist, checked by substring match, and `ConjPieces.lean`'s first 1629 lines are
  `ConjTwist.lean` byte for byte (`cmp`).
- `MulIsogeny` is copied verbatim from `scratch/g0-assemble/parts/40_fibresimple.lean` (VERIFIED by
  `diff`).

## The new and reused leaves, and the remaining glue

### `G0FibreSimple.MulIsogeny` (existing LEAF)

```
∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
  PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)
```

`[n]` is finite and surjective (Mumford, *Abelian varieties*, §4 Application 2 / §6; Milne,
*Abelian varieties*, in Cornell–Silverman 1986, Thm 8.2; UNVERIFIED numbers). This is g0-assemble's
`GluePieces2.mulIsogeny`, so no new leaf is added. Only finiteness of `[n]` is used.

### `HoloHomLift` (new textbook LEAF, N2′)

```
∀ (K : Type) [Field K] (B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
  (ΛB : Submodule ℤ (Fin h → ℂ)) (ΦB : (Fin h → ℂ) → CPts B σ) (Ψ : (Fin g → ℂ) → CPts B σ),
  B.dim = (h : WithBot ℕ∞) → IsUniformization σ ΛB ΦB →
  (∀ z w, Ψ (z + w) = Ψ z * Ψ w) → (∀ U, IsOpen (cDom Ψ U)) →
  (∀ U (s : Γ(B.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U s) (cDom Ψ U)) →
  ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), ∀ z, ΦB (M z) = Ψ z
```

A homomorphism `ℂ^g → B(ℂ)_σ` that is holomorphic in the sense of `IsUniformization` factors
linearly through any uniformization. It is stated over the project's genuine objects (`AbVar`,
`CPts`, `cDom`, `cEvalAt`, `IsUniformization` of `ZInQKernel/HDecomp/LeafPush2/R22.lean`).

**Source.** STANDARD; numbers UNVERIFIED:
- Mumford, *Abelian varieties*, §1: `B(ℂ)_σ ≅ ℂ^h/Λ` as complex Lie groups, with GAGA (Serre
  1956).
- Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1: holomorphic maps of complex tori
  lift to affine maps, and homomorphisms lift to linear maps.

**Why it is true.**
1. On an affine chart the coordinates of `Ψ` are holomorphic on an open set. So `Ψ` is a
   continuous homomorphism, hence a holomorphic one, into the complex Lie group `B(ℂ)_σ`, and
   `Ψ = exp ∘ L` with `L` linear.
2. `Φ_B = exp ∘ T` in the same way. `T` is onto because `Φ_B` is surjective (the image of a
   proper subspace has measure 0), and `h = dim B`, so `T` is an isomorphism.
3. Take `M = T⁻¹L`.

**Why it is smaller than `HomLinearLift`.** It involves one variety and no algebraic morphism.
`HomLinearLift` is its case `Ψ = f ∘ Φ_A`. That algebraic morphisms preserve the holomorphy
predicate is proved in Lean (`cDom_comp`, `cEvalAt_comp`). F3 of conj-twist (`T11a_RiemannEnd`
covers only `End` over `ℂ`) still applies, so a leaf of this kind is needed.

### `ConjHolo` (glue, unproved for non-bijective `s`; STANDARD)

```
∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
  (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Ψ : (Fin g → ℂ) → CPts A σ),
  (∀ U, IsOpen (cDom Ψ U)) →
  (∀ U (t : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U t) (cDom Ψ U)) →
  (∀ V, IsOpen (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)) ∧
  ∀ V (t : Γ((conjVar A s).X.left, V)), DifferentiableOn ℂ
    (fun z => cEvalAt (twistC A σ s h (Ψ (conjL g z))) V t)
    (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)
```

These are exactly the two analytic clauses of `ConjUniformization`, for any holomorphic `Ψ`.

**Why it is true for general `s`.** Cover `A^s = A ×_{Spec K, Spec s} Spec K` by
`W ×_{Spec K} Spec K = Spec(Γ(W) ⊗_{K,s} K)` for affine `W ⊆ A`. A section `Σ aᵢ ⊗ bᵢ` takes at
`twistC(Ψ z̄)` the value `conj(Σ aᵢ(Ψ z̄)·conj σ(bᵢ))`, which is holomorphic in `z`.

**Not needed downstream.** conj-twist's `conjAntiLiftLat_of` uses N3a only for number fields, and
there `conjHolo_of_bijective` proves it.

## What the Lean files prove

### `Artin.lean`: `artinTorsionSurj_of_mulIsogeny : MulIsogeny → ArtinTorsionSurj`

Lemmas:
- `intCast_end_hom`: `((n:ℤ) : End A).hom = (𝟙 A)ⁿ`.
- `comp_mulN`: `Q ≫ [n] = Qⁿ`.
- `isClosed_one_apply`: the unit section is a closed immersion, by Mathlib's
  `isClosedImmersion_of_comp_eq_id`, so its image point is closed.
- `isClosed_singleton_of_mem`: a point of a closed discrete set is closed.
- `mem_range_emb`: an element of `ℂ` integral over `σ(K)` lies in `ι(K̄)`. Proof: `ι(K̄)` is
  algebraically closed, so the minimal polynomial has degree 1.

Proof of the theorem. Let `Q ∈ A(ℂ)_σ` with `Qⁿ = 1`, and let `x` be its image point.
1. `[n](x) = e₀`, the image of the unit section.
2. `[n]` is finite (`MulIsogeny`), so `[n]⁻¹{e₀}` is closed and discrete (Mathlib's
   `isDiscrete_preimage_singleton`). Hence `x` is closed.
3. So `κ(x)` is finite over `K`, by `isClosed_singleton_iff_isClosedImmersion` and
   `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`.
4. `Q = Spec(φ) ≫ (Spec κ(x) → A)` (`Scheme.SpecToEquivOfField`). Since `φ` lands in `ι(K̄)`,
   `φ = ι ∘ ψ`.
5. `P = Spec(ψ) ≫ (Spec κ(x) → A)` satisfies `toC P = Q`.

### `Holo.lean`: `homLinearLift_of_holoHomLift : HoloHomLift → HomLinearLift`

- `cDom_comp` (`rfl`).
- `cEvalAt_comp`: evaluating `s` at `p ≫ φ` is evaluating `φ^* s` at `p`. Proved by unfolding
  `cEvalAt`; the `appLE` identity holds definitionally.
- The theorem applies the leaf to `Ψ = f ∘ Φ_A`.

### `Conj.lean`

**Group-theoretic clauses.** `twistC_mul` (via `homEquiv_mul_conj`), `twistC_surjective` (an
explicit inverse through `conjHomInv`, `mapPtIsoInv` and the adjunction), and
`isUniformization_twist`: given the two analytic clauses, `z ↦ twistC(Φ z̄)` is a uniformization
with kernel `Λ̄`.

**Reduction.** `conjUniformization_of_conjHolo : ConjHolo → ConjUniformization`.

**Analytic lemmas, for bijective `s`:**
- `homEquiv_left_fst` and `twistC_left_fst`: `twistC Q ≫ pr₁ = Spec(conj) ≫ Q`.
- `top_le_of_comp_eq`.
- `eval_of_comp_eq_conj`: the value at `r` of `pr₁^* a` is `conj` of the value of `a` at `q`. The
  proof uses `Scheme.Hom.appLE_comp_appLE` and `Scheme.ΓSpecIso_naturality`.
- `cEvalAt_twistC`.
- `differentiableOn_conj_conj`: `z ↦ conj F(z̄)` is `ℂ`-differentiable on `conj⁻¹D`. Proof:
  `ℝ`-chain rule, then `hasFDerivAt_of_restrictScalars` with the `ℂ`-linear derivative
  `v ↦ conj(L v̄)`.

**`conjHolo_of_bijective`.** `Spec s` is an isomorphism, so `pr₁ : A^s → A` is one too. Every open
of `A^s` is `pr₁⁻¹U`, and every section is `pr₁^* a`.

**`conjUniformizationNF : ConjUniformizationNF`.** Proved outright, using conj-twist's
`ringHom_bijective_of_numberField`.

### `ConjPieces.lean` (assembly)

The file is `ConjTwist.lean` verbatim, followed by the above and these theorems:
- `conjAntiLiftLat_of_homLinearLift : HomLinearLift → ConjAntiLiftLat`. This is conj-twist's
  `conjAntiLiftLat_of` with N3a replaced by `conjUniformizationNF`.
- `conjTwistNontrivial_of_surj_N2`.
- `conjTwistNontrivial_leaves` and `conjTwistFromLeaves_leaves` (displayed above).
- `conjTwistFromLeaves_of_pieces : MulIsogeny → HoloHomLift → ConjHolo → ConjTwistFromLeaves`,
  which goes through conj-twist's unchanged `conjTwistFromLeaves_main`.

## Findings

- **F1 (VERIFIED, compiled). N1-surj needs no new leaf.** It follows from `MulIsogeny`, which is
  already a leaf. Two things are not needed:
  - the `n^{2g}` count (T5 over `ℂ`), which conj-twist's F5 had planned to use;
  - base change to `ℂ`.

  The argument is scheme-theoretic: torsion points lie over closed points, and closed points have
  residue fields algebraic over `K`.
- **F2 (VERIFIED, compiled). N3a is unnecessary for G10.** Its number-field form is a theorem
  (`conjUniformizationNF`). The `ConjUniformization` Prop as stated, quantified over all fields
  and all `s`, is true (STANDARD argument above). It is reduced to `ConjHolo` and proved for
  bijective `s`. Its non-bijective case is the only unproved part, and nothing uses it.
- **F3 (argument). `HomLinearLift` cannot be made glue with the current leaves.** Its analytic
  core is `HoloHomLift`. Proving `HoloHomLift` would need the complex-Lie-group structure of
  `B(ℂ)_σ`, the exponential, and the measure-zero argument; none is in the project or in Mathlib
  for this predicate. So it is a leaf (Mumford §1, BL 1.2.1).
- **F4.** `HomLinearLift`'s hypothesis `A.dim = g` is unused (`homLinearLift_of_holoHomLift`
  ignores it). This is harmless.

## Integration recommendation

Replace conj-twist's `conjTwistFromLeaves_main` with `conjTwistFromLeaves_leaves` (from
`ConjPieces.lean`), followed by g10-odd's `g10GlueConcrete_of_conjTwistFromLeaves`. Then G10's
conjugation core rests on:
- Faltings, T26 and T35 (in the build);
- `MulIsogeny` (already a `GluePieces2` leaf);
- the single new textbook leaf `HoloHomLift`.

No glue remains.
