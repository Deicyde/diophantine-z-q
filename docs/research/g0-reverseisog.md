# g0-reverseisog: the glue piece `ReverseIsogeny` (G17 after Poincaré)

## Result

**`ReverseIsogeny` is proved in Lean.** The proof uses two leaves already in the bundle
(`ResearchLeaves.r19`, which is Gaudron-Rémond R19, and `ResearchLeaves.h5`, H5's finiteness of the
stable height) and piece 1, `DimFinite`. It adds no new leaf. So `HSyn.glueOutputs_of_leaves` and
`HSyn.sixContactMin_of_leaves` now need **nine** glue pieces instead of ten:

```lean
theorem HSyn.G0RevIsog.reverseIsogeny_of_leaves (r : ResearchLeaves) (hDimF : G0Split.DimFinite) :
    G0Split.ReverseIsogeny
theorem HSyn.glueOutputs_of_leaves_rev (r t hR18 hR22 hDimF hDim hBelyi hSimp hAdd hBC hProdE
    hThetaPt hMod) : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul      -- no `hRev`
theorem HSyn.sixContactMin_of_leaves_rev (r t hR18 hR22) (m : MissingPiecesRev) : ZInQ.SixContactMin
```

(VERIFIED: `scratch/g0-reverseisog/SplitRev.lean` compiles with 0 errors and no `sorry`, in
2m57s. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all four declarations.
The first 20024 lines of `SplitRev.lean` are byte-identical to `scratch/g0-split/Split.lean` at
wip/g0-split c20fa62b: the sha256 sums match.)

The statement was not changed. Section 2 of `ReverseIsogeny.lean` is a verbatim copy of
`G0Split.ReverseIsogeny`, and `SplitRev.lean` contains Split.lean's own declaration unchanged.

There is a second route that is independent of heights (Route A). It uses one textbook leaf,
`IsogenyQuasiInverse` (Mumford; Milne), and nothing else, not even `DimFinite`:
`G0RevIsog.reverseIsogeny : IsogenyQuasiInverse → G0Split.ReverseIsogeny` (VERIFIED: compiles in
the Mathlib-only file `scratch/g0-reverseisog/ReverseIsogeny.lean`, standard axioms).

## The piece (unchanged)

`ReverseIsogeny` (Split.lean, `G0Split`) says the following. Let `L` be a number field and `A, J, Z`
abelian varieties over `L` (`PkgI3.AbVar`). Let `P` be an abelian variety (def-faltings' `AbVar`)
with `IsProductOf P.X A.X Z.X`, meaning homomorphisms `p₁, p₂` such that `(p₁, p₂)` is an
isomorphism. Let `f : A → J` and `g : Z → J` be homomorphisms such that
`fst ≫ f + snd ≫ g : A × Z → J` is finite and surjective. Then there is an isogeny
`φ : J → P` (`ZInQ.DefFaltings.IsIsogeny`: a monoid homomorphism that is finite and surjective),
and `J.dim = P.dim`.

## Decomposition

| name | kind | content | status |
|---|---|---|---|
| `isogeny_of_product` | glue | `h = f∘p₁ + g∘p₂ : P → J` is an isogeny. It equals `(p₁,p₂) ≫ (fst≫f + snd≫g)` (`comp_mul`, `lift_fst`); it is a homomorphism because `J` is commutative; finite and surjective are stable under composition, and an isomorphism has both | **proved** |
| `topologicalKrullDim_le_of_specializing` | glue (topology) | if `f : X → Y` is continuous, specializing and surjective and `Y` is quasi-sober, then `dim Y ≤ dim X`. Chains of irreducible closed sets lift along `f` (`lift_series`, by induction on the chain with `RelSeries.inductionOn'`) | **proved** |
| `dim_le_of_finite_surjective` | glue | a finite surjective morphism of schemes `X → Y` gives `dim Y ≤ dim X` (finite ⇒ integral ⇒ universally closed ⇒ closed map ⇒ specializing; Mathlib) | **proved** |
| `dim_eq_of_isogenies` | glue | isogenies `A → B` and `B → A` give `dim A = dim B` | **proved** |
| `IsogenyReverseExists` | interface | over a number field, an isogeny `A → B` has an isogeny `B → A` | proved from either route |
| `reverseIsogeny_of_exists` | glue | `IsogenyReverseExists → ReverseIsogeny` | **proved** |
| Route B: `isogenyReverseExists_of_r19` | glue | from `R19_GaudronRemond` (isogenies in both directions), `StableHeightFinite` (the input `h_F(A) = x ∈ ℝ`) and `DimFinite` (the input `dim A = g ∈ ℕ`) | **proved** |
| Route A: `IsogenyQuasiInverse` | **leaf (textbook)** | an isogeny `φ : A → B` over a field has an isogeny `ψ : B → A` and an `n ≥ 1` with `ψ∘φ = [n]_A` and `φ∘ψ = [n]_B` | leaf, stated |

Dimension clause. The piece's `dim J = dim P` takes no new leaf. A closed surjective map cannot
lower Krull dimension, and there are isogenies both ways (`h : P → J` from the product and `ψ` back),
so the two inequalities give equality. Proving it this way avoids the harder fact that integral
morphisms have zero-dimensional fibres (incomparability). The topological lemma is general and may
be reused, for example by `DimBaseChange`.

Why Route B is legitimate. R19 is the published statement of Gaudron-Rémond (Duke Math. J. 163
(2014), Thm 1.4, as already recorded in the bundle; locators.md). It gives isogenies in both
directions with a degree bound. Route B uses only the existence of the backward isogeny, which is
weaker than the published statement. Its hypotheses `A.dim = g` and `stableFaltingsHeight A = x`
are supplied by `DimFinite` (piece 1, in progress on another task) and by H5's finiteness
`r.h5.1`. `glueOutputs_of_leaves` already uses both: it takes `hDimF`, and it uses `r.h5.1` for
`faltingsHeight_coe`.

Route B inherits H5's caveat (h-decomposition, leaf-adopt F2: `StableHeightFinite` is "published
theorem + correctness of the definition"). Route A has no such caveat.

## The leaf of Route A

```lean
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
    ZInQ.DefFaltings.IsIsogeny φ →
    ∃ (ψ : B.X ⟶ A.X) (n : ℕ), 0 < n ∧ ZInQ.DefFaltings.IsIsogeny ψ ∧
      φ ≫ ψ = (𝟙 A.X) ^ n ∧ ψ ≫ φ = (𝟙 B.X) ^ n
```

* Definitions are genuine: def-faltings' `AbVar` (a group object in `Over (Spec K)` that is proper,
  smooth and geometrically integral) and `IsIsogeny` (`IsMonHom` ∧ `IsFinite` ∧ `Surjective`).
  `(𝟙 A.X) ^ n` is `[n]_A` in Mathlib's group of morphisms into a group object. VERIFIED:
  `(𝟙 A.X) ^ 2 = lift (𝟙 A.X) (𝟙 A.X) ≫ μ[A.X]` by `pow_two; rfl`, compiled.
* Sources (STANDARD; theorem numbers UNVERIFIED, from memory, no network): Mumford, *Abelian
  Varieties*, §7 (quotients by finite group schemes) and the remark on isogenies there, over an
  algebraically closed field; Milne, *Abelian Varieties*, course notes (2008), I §7 (an isogeny of
  degree `n` has `β` with `β∘α = n_A`, `α∘β = n_B`), over an arbitrary field. Milne's definition
  of isogeny (a surjective homomorphism with finite kernel, equivalently finite flat surjective) agrees
  with `IsIsogeny`, because a finite surjective homomorphism has finite kernel, and an isogeny in
  Milne's sense is finite.
* Proving the leaf needs quotients of abelian varieties by finite subgroup schemes, the order of a
  finite group scheme, and Deligne's theorem that a finite commutative group scheme is killed by
  its order. None of these is in Mathlib 4.35 (prereq-survey). In characteristic 0 the kernel is
  étale, which simplifies the last two steps but not the quotient.

## Files

* `scratch/g0-reverseisog/ReverseIsogeny.lean`: imports only Mathlib, about 2.5 min. It contains
  verbatim copies of the definitions the piece needs, Route A, the interface, and the dimension glue.
* `scratch/g0-reverseisog/SplitRev.lean`: Split.lean verbatim plus §3″. It contains the same glue,
  Route B, `glueOutputs_of_leaves_rev`, `MissingPiecesRev` and `sixContactMin_of_leaves_rev`.
  Before checking it, build the upstream helpers once:
  `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`.
* `scratch/g0-reverseisog/log.md`: compile log.

## For integration

Replace `hRev` in `glueOutputs_of_leaves` with `G0RevIsog.reverseIsogeny_of_leaves r hDimF`, and
drop `reverseIsogeny` from `MissingPieces`. The proofs refer only to the declarations of Split.lean
named above, so they should transfer when Split.lean is adopted; that transfer has not been
compiled. If the leaf bundle is reorganized so that R19 is no longer present, switch to Route A
(`reverseIsogeny`, one textbook leaf).
