# glue-I3-linalg: the linear-algebra glue of package I3 (steps C2, E1)

Status: research note (task glue-I3-linalg, 2026-11-11). Lean: `scratch/glue-I3-linalg/Commutant.lean`
(251 lines, no `sorry`, compiles with `lake env lean`), with `scratch/glue-I3-linalg/I3.lean` (verbatim copy of
pkg-I3's object layer, not modified). Log: `scratch/glue-I3-linalg/log.md`. Marks: VERIFIED (compiled or read),
STANDARD (published, exact reference), SPECULATIVE; UNVERIFIED for locators given from memory.

## Main result

**C2's commutant argument is proved in Lean (VERIFIED, compiled; axioms `propext`, `Classical.choice`,
`Quot.sound`), over Mathlib's genuine `Representation`, `IsSemisimpleRepresentation` and `IsIrreducible`.** Two
further linear-algebra facts are needed. They are stated in Lean as `def … : Prop` but not proved: invariants
under extension of coefficients, and semisimplicity under extension in characteristic 0. Neither is a literature
leaf; both are textbook algebra. From these two, Lean proves the absolute irreducibility of `r_ℓ` that N5
L731-734 needs.

| Lean name (`GlueI3.`) | Statement | Status |
| --- | --- | --- |
| `isIrreducible_of_commutant_scalar` | `ρ : Representation k G V`, `V ≠ 0`, `ρ` semisimple, every `G`-equivariant `φ : V →ₗ V` is a scalar ⇒ `ρ.IsIrreducible` | proved |
| `commOf r`, `blockMap`, `blockMap_injective` | the commutant `End_G` as a `k`-submodule; the injection `End_G(V)⁴ ↪ End_G(V ⊕ V)`, `(a,b,c,d) ↦ [[a,b],[c,d]]` | proved |
| `finrank_commOf_eq_one_of_prod_le_four` | `V ≠ 0` finite-dimensional, `dim End_G(V ⊕ V) ≤ 4` ⇒ `dim End_G(V) = 1` | proved |
| `isIrreducible_of_finrank_commOf_prod_le_four` | in addition `ρ` semisimple ⇒ `ρ` irreducible and `End_G(V) = k` | proved |
| `repBaseChange E ρ` | `ρ_E(g) = ρ(g) ⊗ E` on `E ⊗_k V`, a Mathlib `Representation` (laws proved) | definition |
| `InvariantsBaseChange` | `V` finite-dimensional ⇒ `dim_E End_G(V ⊗ E) = dim_k End_G(V)` | **stated, not proved** |
| `SemisimpleBaseChange` | `char k = 0`, `V` finite-dimensional, `ρ` semisimple ⇒ `ρ_E` semisimple | **stated, not proved** |
| `absolutelyIrreducible_of_finrank_commOf_prod_le_four` | from the two Props above: `char k = 0`, `V ≠ 0` finite-dimensional, `ρ` semisimple, `dim End_G(V ⊕ V) ≤ 4` ⇒ `ρ_F` irreducible for **every** field `F ⊇ k` | proved (conditional on the two Props) |

## 1. How this is the argument of N5 L731-734 (C2)

N5 argues as follows:
- by Faltings, `V_ℓ(A)|G_{L'}` is semisimple with `End_G(V_ℓ A) = B ⊗ ℚ_ℓ`;
- over `E ⊇ ℚ_ℓ` splitting `B`, `V_ℓ A ⊗ E = r ⊕ r`;
- the commutant of `r` is then scalar, so `r` is absolutely irreducible.

In Lean terms (`G = G_{L'}`, `k = E`, `ρ = r`):

1. `dim_{ℚ_ℓ} End_G(V_ℓ A) = rank_ℤ End_{L'}(A) = 4`. The first equality is pkg-I3's `finrank_equivEnd`
   (proved there from `FaltingsTate`, `TateModuleFree` and `HomFreeFinite`). The value 4 comes from
   `End_{L'}(A) ⊗ ℚ = B`, the output of A9, A10 and A8/B3 (not I3).
2. `InvariantsBaseChange` gives `dim_E End_G(V_ℓ A ⊗ E) = 4`.
3. `V_ℓ A ⊗ E ≅ r ⊕ r` as `G`-representations (from `B ⊗ E ≅ M₂(E)`: the idempotent `e₁₁` cuts out `r`, and
   `e₁₂` gives `e₂₂V ≅ e₁₁V`). Transport along this isomorphism gives `dim_E End_G(r ⊕ r) ≤ 4`. **Not
   formalized** (see §3).
4. `r` is semisimple: it is a summand of `V_ℓ A ⊗ E`, which is semisimple by `FaltingsSemisimple` and
   `SemisimpleBaseChange`. A summand of a semisimple representation is semisimple; Mathlib has this for
   modules (`IsSemisimpleModule` of a submodule), but the transfer was not written.
5. `absolutelyIrreducible_of_finrank_commOf_prod_le_four` concludes.

**Remark (VERIFIED by the proof).** N5 says "dimension 4, so `End_G r = E`". The Lean proof uses only the
inequality `4 · dim End_G(r) ≤ dim End_G(r ⊕ r) ≤ 4`, through the injective block map. The reverse inclusion
`End_G(r ⊕ r) = M₂(End_G r)` is not needed.

## 2. E1 (VERIFIED where stated; otherwise the reason is given)

- *Common constituent → nonzero equivariant `ℚ_ℓ`-map → nonzero `Hom`.* The last arrow is pkg-I3's
  `exists_hom_ne_zero_of_equivariant` (proved). The first arrow needs two facts:
  - a common constituent over `E` of two semisimple representations gives a nonzero `E`-linear equivariant
    map (compose the projection onto the summand with the inclusion; `projection_comm` here proves that the
    projection is equivariant);
  - descent of a nonzero `E`-equivariant map `V_A ⊗ E → V_J ⊗ E` to a nonzero `ℚ_ℓ`-equivariant map. This is
    the `Hom` version of `InvariantsBaseChange`: the commutant computation applies verbatim to `Hom_G(V, W)`.

  Not formalized.
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

1. **`InvariantsBaseChange` (and its `Hom` version), proof.** STANDARD (e.g. Bourbaki, *Algèbre* II §3, or
   any proof that kernels commute with flat base change; UNVERIFIED locator). The Lean route: the commutant of
   `ρ(G)` equals the commutant of a finite spanning subfamily `ρ(g₁), …, ρ(g_m)` (`End_k V` is
   finite-dimensional). So it is the kernel of `Φ : End V → (End V)^m`. Then `End_E(V_E) ≅ E ⊗ End_k V`
   (finite free), and kernels commute with the flat base change `k → E`. Every ingredient is in Mathlib, but
   the bookkeeping did not fit in this run (the task began at 22:24 for a 23:20 deadline). Estimate: 150-300
   lines.
2. **`SemisimpleBaseChange`, proof.** STANDARD (Bourbaki, *Algèbre* VIII §12, separable semisimple
   algebras; Curtis–Reiner §69; UNVERIFIED locators). Mathlib v4.35.0 has semisimple rings and modules, but
   I did not find "a finite-dimensional semisimple algebra over a perfect field stays semisimple after base
   change" (not searched exhaustively; SPECULATIVE). This is the hardest of the remaining linear-algebra
   items. Alternative avoiding it: absolute irreducibility only needs `ρ_F` irreducible. A representation
   whose commutant stays `F` after every extension is absolutely irreducible by Burnside's theorem
   (`F[ρ(G)] = End V` over `F̄`), and Burnside's theorem gives irreducibility over every `F` directly,
   without semisimplicity of `ρ_F`. Mathlib has no Burnside density theorem (SPECULATIVE; not found by name).
3. **`V_ℓ A ⊗ E ≅ r ⊕ r` from `B ⊗ E ≅ M₂(E)`** (C2 step 3) and the summand-is-semisimple transfer (step 4):
   routine, not written for lack of time.
4. **`T_ℓ` under base change of the field.** For `L/K` and a `K`-embedding `K̄ → L̄`, an isomorphism
   `T_ℓ(A) ≅ T_ℓ(A_L)` equivariant along `G_L → G_K`. It uses the universal property of `Over.pullback`
   (`(A_L)(L̄) = A(L̄)`, by `pullback.lift`) and the restriction to `ℓ`-power torsion
   (`A(K̄)[ℓⁿ] = A(L̄)[ℓⁿ]`, which needs `A[ℓⁿ]` étale, i.e. finite and reduced: content of Mumford §4/§6, not
   in `TateModuleFree` as stated). **Finding (SPECULATIVE, but I believe it correct):** the second half is not
   pure glue. `TateModuleFree` gives freeness over each field separately, and the comparison map
   `T_ℓ(A) → T_ℓ(A_L)` is injective but need not be onto from the leaves alone, because they say nothing about
   `A(K̄)[ℓⁿ] → A(L̄)[ℓⁿ]`. The rank equality `2 dim A = 2 dim A_L` would force a finite-index inclusion, and
   saturation needs more. Proposed extra leaf (STANDARD, Mumford §6 Application 2 / Milne 1986 Thm 8.2;
   UNVERIFIED locators): for an algebraically closed `Ω ⊇ k̄` with `ℓ ≠ char k`, `A(k̄)[ℓⁿ] → A(Ω)[ℓⁿ]` is
   bijective. Not written in Lean because the heavy `I3.lean` object layer was not recompiled in this run.
5. **E1's `PoincareReducibility` application**: §2, items (a)-(c); (c) needs the leaf adjustment
   recommended there.

## 4. What compiles (VERIFIED, 2026-11-11 22:31 PST)

`lake env lean scratch/glue-I3-linalg/Commutant.lean` reports no errors and prints:

```
'GlueI3.isIrreducible_of_commutant_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.isIrreducible_of_finrank_commOf_prod_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Commutant.lean` imports only Mathlib (`RepresentationTheory.Semisimple`, `.Irreducible`,
`LinearAlgebra.Projection`, `LinearAlgebra.FiniteDimensional.Basic`). It is independent of the
algebraic-geometry layer and applies to `galRep` of `I3.lean`, because `galRep ℓ A` is a Mathlib
`Representation ℚ_[ℓ] G_K (V_ℓ A)` and pkg-I3's `equivEnd A ℓ` is exactly `commOf (fun σ => galRep ℓ A σ)`
(same carrier).
