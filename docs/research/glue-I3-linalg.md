# glue-I3-linalg: the linear-algebra glue of package I3 (steps C2, E1)

Status: research note (task glue-I3-linalg, 2026-11-11). Lean files in `scratch/glue-I3-linalg/`, none
containing `sorry`, all compiled with `lake env lean`:
- `Commutant.lean` (467 lines, Mathlib only): the linear algebra;
- `TateBC.lean` (191 lines): Tate modules along injective maps;
- `C2.lean` (1270 lines): pkg-I3's `I3.lean` verbatim, plus the body of `Commutant.lean`, plus C2 and E1
  stated and proved over the object layer;
- `I3.lean`: a verbatim copy of pkg-I3's file.

Log: `scratch/glue-I3-linalg/log.md`. Marks: VERIFIED (compiled or read), STANDARD (published, exact
reference), SPECULATIVE; UNVERIFIED for locators given from memory.

## Main result

**The I3 glue for C2 and E1 is proved in Lean over pkg-I3's object layer (VERIFIED, compiled; axioms
`propext`, `Classical.choice`, `Quot.sound`), modulo one textbook algebra statement, which is stated in Lean
but not proved: `SemisimpleBaseChange`.** Everything is over Mathlib's genuine `Representation`, `IsSemisimpleRepresentation`
and `IsIrreducible`.

- `PkgI3.C2_absolutelyIrreducible` (N5 L731-734). From the leaves `FaltingsSemisimple`, `FaltingsTate`,
  `TateModuleFree` and `HomFreeFinite`, together with:
  - A9's output `rank_ℤ End_K(A) = 4`;
  - an equivariant `E ⊗ V_ℓ(A) ≅ r ⊕ r` (from `B ⊗ E ≅ M₂(E)`);

  it proves that `r` is absolutely irreducible.
- `PkgI3.E1_exists_hom_ne_zero` (N5 L861-867, first half). From the leaves `FaltingsSemisimple`,
  `FaltingsTate` and `TateModuleFree`, a common constituent of `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` gives a nonzero
  `Hom_K(A, J)`.
- Unproved glue: only `SemisimpleBaseChange` (used by both): semisimplicity survives extension of scalars in
  characteristic 0. It is not a literature leaf; it is STANDARD algebra. §3 gives the route and the reason it
  was not done.
- Invariants under extension of coefficients are **proved**:
  - `finrank_commOf_baseChange_le`: `dim_E End_G(E ⊗ V) ≤ dim_k End_G(V)`;
  - `scalar_commOf_baseChange`: a scalar commutant stays scalar;
  - `equivariantDescent`.

  So an earlier stated Prop, `InvariantsBaseChange`, was dropped.
- Not done:
  - the application of `PoincareReducibility` in E1. It needs `EndDivision A`, and the leaf interface (A9's
    output) has to be adjusted; see §2;
  - the geometric half of `T_ℓ` under base change. Its algebraic core is proved (`Tate.map_bijective`).

| Lean name (`GlueI3.`) | Statement | Status |
| --- | --- | --- |
| `isIrreducible_of_commutant_scalar` | `ρ : Representation k G V`, `V ≠ 0`, `ρ` semisimple, every `G`-equivariant `φ : V →ₗ V` is a scalar ⇒ `ρ.IsIrreducible` | proved |
| `commOf r`, `blockMap`, `blockMap_injective` | the commutant `End_G` as a `k`-submodule; the injection `End_G(V)⁴ ↪ End_G(V ⊕ V)`, `(a,b,c,d) ↦ [[a,b],[c,d]]` | proved |
| `finrank_commOf_eq_one_of_prod_le_four` | `V ≠ 0` finite-dimensional, `dim End_G(V ⊕ V) ≤ 4` ⇒ `dim End_G(V) = 1` | proved |
| `isIrreducible_of_finrank_commOf_prod_le_four` | in addition `ρ` semisimple ⇒ `ρ` irreducible and `End_G(V) = k` | proved |
| `repBaseChange E ρ` | `ρ_E(g) = ρ(g) ⊗ E` on `E ⊗_k V`, a Mathlib `Representation` (laws proved) | definition |
| `commBaseChange`, `commOf_baseChange_le_range` | every `G`-equivariant `E`-endomorphism of `E ⊗ V` is the image of `E ⊗ End_G(V)` (`V` finite-dimensional; coordinates in a `k`-basis of `E`) | proved |
| `finrank_commOf_baseChange_le` | `dim_E End_G(E ⊗ V) ≤ dim_k End_G(V)` | proved |
| `scalar_commOf_baseChange` | `End_G(V) = k` ⇒ `End_G(E ⊗ V) = E` | proved |
| `SemisimpleBaseChange` | `char k = 0`, `V` finite-dimensional, `ρ` semisimple ⇒ `ρ_E` semisimple | **stated, not proved** |
| `exists_equivariant_ne_zero_of_common` | E1's first arrow: `ρ` semisimple, a nonzero subrepresentation `U` of `ρ` equivariantly isomorphic to a subrepresentation `U'` of `σ` ⇒ a nonzero `G`-equivariant linear map `V → W` | proved |
| `PkgI3.Tate.map_bijective` (`TateBC.lean`) | `φ : M →+ N` injective, `T_ℓ M` free and finite, `T_ℓ N` finite, equal ranks ⇒ `T_ℓ(φ)` bijective (the algebraic core of `T_ℓ` under base change) | proved |
| `finrank_commOf_le_of_equiv` (`C2.lean`) | an equivariant linear isomorphism `V ≃ W` gives `dim End_G V ≤ dim End_G W` | proved |
| `isSemisimple_of_surjective` | semisimplicity passes to equivariant quotients | proved |
| `exists_equivariant_ne_zero_of_baseChange`, `equivariantDescent` | nonzero equivariant `E`-map `V⊗E → W⊗E` ⇒ nonzero equivariant `k`-map `V → W` | proved |
| `PkgI3.E1_exists_hom_ne_zero` (`C2.lean`) | E1: common constituent over `E` ⇒ nonzero `Hom A J` (see above) | proved (conditional on `SemisimpleBaseChange`) |
| `PkgI3.C2_absolutelyIrreducible` (`C2.lean`) | C2 over the object layer (see above) | proved (conditional on `SemisimpleBaseChange` and the isomorphism `e`) |
| `absolutelyIrreducible_of_finrank_commOf_prod_le_four` | from `SemisimpleBaseChange`: `char k = 0`, `V ≠ 0` finite-dimensional, `ρ` semisimple, `dim End_G(V ⊕ V) ≤ 4` ⇒ `ρ_F` irreducible for **every** field `F ⊇ k` | proved (conditional on `SemisimpleBaseChange`) |

**C2 in pkg-I3's object layer (VERIFIED, compiled, `C2.lean`).** `PkgI3.C2_absolutelyIrreducible` has these
hypotheses:
- the leaves `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree`, `HomFreeFinite`;
- the glue Prop `SemisimpleBaseChange`;
- A9's output in the form `finrank ℤ (End A) = 4`;
- a field `E ⊇ ℚ_ℓ`, a representation `r` of `G_K` on a nonzero finite-dimensional `U`, and a
  `G_K`-equivariant `E`-linear isomorphism `E ⊗ V_ℓ(A) ≃ U × U`.

It concludes that `r ⊗ F` is irreducible for every field `F ⊇ E`. The semisimplicity of `r` is derived in
Lean: `E ⊗ V_ℓ A` is semisimple by `FaltingsSemisimple` and `SemisimpleBaseChange`, and `r` is an equivariant
quotient of it (`isSemisimple_of_surjective`). The isomorphism `E ⊗ V_ℓ A ≃ U × U` is A9/A10's input; it
comes from `B ⊗ E ≅ M₂(E)` and is not formalized.

**E1's first half in pkg-I3's object layer (VERIFIED, compiled, `C2.lean`).** `PkgI3.E1_exists_hom_ne_zero`
has these hypotheses:
- the leaves `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree`;
- `SemisimpleBaseChange` (the only unproved glue it uses). The descent step, `EquivariantDescent` (a nonzero
  `G`-equivariant `E`-linear map `V ⊗ E → W ⊗ E` gives a nonzero `G`-equivariant `k`-linear map `V → W`), is
  **proved** (`equivariantDescent`: expand in a `k`-basis of `E` and take a nonzero coordinate);
- a common constituent: a nonzero subrepresentation of `V_ℓ(A) ⊗ E` equivariantly isomorphic to a
  subrepresentation of `V_ℓ(J) ⊗ E`.

It concludes that there is a nonzero `f : Hom A J` over `K`. This is N5 L861-867 up to the application of
`PoincareReducibility` (§2).

## 1. How this is the argument of N5 L731-734 (C2)

N5 argues as follows:
- by Faltings, `V_ℓ(A)|G_{L'}` is semisimple with `End_G(V_ℓ A) = B ⊗ ℚ_ℓ`;
- over `E ⊇ ℚ_ℓ` splitting `B`, `V_ℓ A ⊗ E = r ⊕ r`;
- the commutant of `r` is then scalar, so `r` is absolutely irreducible.

In Lean terms (`G = G_{L'}`, `k = E`, `ρ = r`):

1. `dim_{ℚ_ℓ} End_G(V_ℓ A) = rank_ℤ End_{L'}(A) = 4`. The first equality is pkg-I3's `finrank_equivEnd`
   (proved there from `FaltingsTate`, `TateModuleFree` and `HomFreeFinite`). The value 4 comes from
   `End_{L'}(A) ⊗ ℚ = B`, the output of A9, A10 and A8/B3 (not I3).
2. `finrank_commOf_baseChange_le` (proved) gives `dim_E End_G(V_ℓ A ⊗ E) ≤ 4`.
3. `V_ℓ A ⊗ E ≅ r ⊕ r` as `G`-representations (from `B ⊗ E ≅ M₂(E)`: the idempotent `e₁₁` cuts out `r`, and
   `e₁₂` gives `e₂₂V ≅ e₁₁V`). The isomorphism itself is **not formalized** (it is the hypothesis `e`; see
   §3). Transport along it (`finrank_commOf_le_of_equiv`, proved) gives `dim_E End_G(r ⊕ r) ≤ 4`.
4. `r` is semisimple: it is an equivariant quotient of `V_ℓ A ⊗ E`, which is semisimple by
   `FaltingsSemisimple` and `SemisimpleBaseChange`. Proved (`isSemisimple_of_surjective`).
5. `absolutelyIrreducible_of_finrank_commOf_prod_le_four` concludes. It shows `End_G(r) = E`, then
   `End_G(r ⊗ F) = F` by `scalar_commOf_baseChange`, and `r ⊗ F` is semisimple by `SemisimpleBaseChange`.
   Hence `r ⊗ F` is irreducible.

**Remark (VERIFIED by the proof).** N5 says "dimension 4, so `End_G r = E`". The Lean proof uses only the
inequality `4 · dim End_G(r) ≤ dim End_G(r ⊕ r) ≤ 4`, through the injective block map. The reverse inclusion
`End_G(r ⊕ r) = M₂(End_G r)` is not needed.

## 2. E1 (VERIFIED where stated; otherwise the reason is given)

- *Common constituent → nonzero equivariant `ℚ_ℓ`-map → nonzero `Hom`.* The last arrow is pkg-I3's
  `exists_hom_ne_zero_of_equivariant` (proved). The first arrow needs two facts:
  - a common constituent over `E` gives a nonzero `E`-linear equivariant map: **proved here**
    (`exists_equivariant_ne_zero_of_common`). Only the source needs to be semisimple, which is
    `FaltingsSemisimple` + `SemisimpleBaseChange` for `V_ℓ(A) ⊗ E`; N5 invokes the semisimplicity of `V(J)`,
    but either side suffices;
  - descent of a nonzero `E`-equivariant map `V_A ⊗ E → V_J ⊗ E` to a nonzero `ℚ_ℓ`-equivariant map. This is
    the `Hom` version of invariants under extension. It is **proved** as `equivariantDescent`.

  The two arrows are assembled in `PkgI3.E1_exists_hom_ne_zero` (compiled).
- *Application of `PoincareReducibility`.* That leaf needs `EndDivision A` over `L'` (every nonzero
  `f ∈ End_{L'}(A)` finite and surjective). N5 gets it from `End⁰(A_{ℚ̄}) = B` (a division algebra). Lean
  would need:
  - (a) faithfulness of base change on `Hom` (`End_{L'}(A) ↪ End_{ℚ̄}(A_{ℚ̄})`), which follows from
    `Over.pullback` along `Spec ℚ̄ → Spec L'`, a faithfully flat base change;
  - (b) descent of "finite and surjective" along `Spec ℚ̄ → Spec L'`. Mathlib has fpqc descent for these
    properties (UNVERIFIED by grep in this run);
  - (c) "a nonzero element of a division algebra is invertible, hence an isogeny" in the isogeny category,
    which needs `End0` units to give quasi-inverse isogenies.

  Item (c) is where a design choice is needed. `EndDivision` is phrased as "nonzero ⇒ isogeny", while A9's
  output is an algebra isomorphism `End0 ≃ₐ B`. Bridging them needs "a unit of `End⁰` is an isogeny", which
  holds in the isogeny category but is not derivable from the current I3 leaves. **Recommendation
  (SPECULATIVE):** restate A9's output, or add to the QMDichotomy leaf, in the form `EndDivision`, which is
  what E1 consumes. Otherwise add Mumford §19 Cor. 2's statement "`A` is simple iff every nonzero
  endomorphism is an isogeny" as part of `PoincareReducibility`'s source. Not formalized.

## 3. What remains, with the reason

1. **Invariants under extension of coefficients: done.** (`commOf_baseChange_le_range`,
   `finrank_commOf_baseChange_le`, `scalar_commOf_baseChange`, `equivariantDescent`, all proved, 22:42-22:47
   PST.) Only `≤` is proved. `≥` is not needed by C2 or E1.
2. **`SemisimpleBaseChange`, proof.** STANDARD (Bourbaki, *Algèbre* VIII §12, separable semisimple
   algebras; Curtis–Reiner §69; UNVERIFIED locators). Mathlib v4.35.0 has semisimple rings and modules, but
   I did not find "a finite-dimensional semisimple algebra over a perfect field stays semisimple after base
   change" (not searched exhaustively; SPECULATIVE). This is the hardest of the remaining linear-algebra
   items. Alternative avoiding it: absolute irreducibility only needs `ρ_F` irreducible. A representation
   whose commutant stays `F` after every extension is absolutely irreducible by Burnside's theorem
   (`F[ρ(G)] = End V` over `F̄`), and Burnside's theorem gives irreducibility over every `F` directly,
   without semisimplicity of `ρ_F`. Mathlib has no Burnside density theorem (SPECULATIVE; not found by name).
3. **`V_ℓ A ⊗ E ≅ r ⊕ r` from `B ⊗ E ≅ M₂(E)`** (C2 step 3): routine, but not written for lack of time.
   It is the hypothesis `e` of `C2_absolutelyIrreducible`. The transport of commutant dimensions along `e` is
   proved (`finrank_commOf_le_of_equiv`), and so is the semisimplicity of `r` (step 4).
4. **`T_ℓ` under base change of the field.** For `L/K` and a `K`-embedding `K̄ → L̄`, we want an
   isomorphism `T_ℓ(A) ≅ T_ℓ(A_L)` that is equivariant along `G_L → G_K`. Argument (VERIFIED as an
   argument, not formalized):
   - the universal property of `Over.pullback` gives `(A_L)(L̄) = A(L̄)` (`pullback.lift`);
   - `A(K̄) → A(L̄)` is injective, because a morphism from the spectrum of a field is a point together
     with an embedding of its residue field;
   - so `Tate.map` gives an injective map `T_ℓ(A) → T_ℓ(A_L)`;
   - its image is saturated: if `ℓx = ι(y)`, then `x_{n-1} = y_n ∈ A(K̄)` for every `n`, so `x ∈ ι(T_ℓ A)`;
   - the cokernel is therefore a finitely generated torsion-free `ℤ_ℓ`-module (`TateModuleFree` over `L`).
     Its rank is `2 dim A_L − 2 dim A = 0` (`TateModuleFree` over `K` and over `L`), so it is zero.

   This is glue, given one more geometric fact: `dim A_L = dim A` (the Krull dimension of a variety is
   invariant under field extension), which is not in Mathlib in this form (SPECULATIVE; not searched).
   **The algebraic core is proved** (`scratch/glue-I3-linalg/TateBC.lean`, VERIFIED, compiled; axioms
   `propext`, `Classical.choice`, `Quot.sound`). `PkgI3.Tate.map_bijective`: if `φ : M →+ N` is injective,
   `T_ℓ M` is free and finite, `T_ℓ N` is finite, and the finranks are equal, then
   `Tate.map φ : T_ℓ M → T_ℓ N` is bijective. Its proof goes through saturation (`mem_range_of_ell_smul`),
   torsion-freeness of the cokernel (`mem_range_of_smul`) and rank–nullity over `ℤ_ℓ`. **What remains** is the
   geometric half, on the `I3.lean` object layer, which was not recompiled in this run:
   - `A(K̄) → A(L̄) ≅ A_L(L̄)` is an injective group homomorphism;
   - it is compatible with `G_L → G_K`;
   - `dim A_L = dim A`.
5. **E1's `PoincareReducibility` application**: §2, items (a)-(c); (c) needs the leaf adjustment
   recommended there.

## 4. What compiles (VERIFIED, 2026-11-11; last runs 22:46-22:47 PST)

`lake env lean scratch/glue-I3-linalg/C2.lean` (about 15 s) reports no errors and prints:

```
'PkgI3.C2_absolutelyIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'PkgI3.E1_exists_hom_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.equivariantDescent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean scratch/glue-I3-linalg/TateBC.lean` reports no errors and prints
`'PkgI3.Tate.map_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]`.

`lake env lean scratch/glue-I3-linalg/Commutant.lean` reports no errors and prints:

```
'GlueI3.isIrreducible_of_commutant_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.isIrreducible_of_finrank_commOf_prod_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.exists_equivariant_ne_zero_of_common' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.isSemisimple_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.exists_equivariant_ne_zero_of_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.finrank_commOf_baseChange_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.scalar_commOf_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Commutant.lean` imports only Mathlib (`RepresentationTheory.Semisimple`, `.Irreducible`,
`LinearAlgebra.Projection`, `LinearAlgebra.FiniteDimensional.Basic`). It is independent of the
algebraic-geometry layer and applies to `galRep` of `I3.lean`, because `galRep ℓ A` is a Mathlib
`Representation ℚ_[ℓ] G_K (V_ℓ A)` and pkg-I3's `equivEnd A ℓ` is exactly `commOf (fun σ => galRep ℓ A σ)`
(same carrier).
