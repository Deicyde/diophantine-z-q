# g0-dim: the glue pieces `DimFinite` and `DimBaseChange`, proved

Task g0-dim, 2026-11-13. Lean: `scratch/g0-dim/Dim.lean` (standalone, imports only Mathlib) and
`scratch/g0-dim/part_dim.lean` (the same proofs appended to g0-split's `Split.lean` by
`scratch/g0-dim/build.sh`, giving `SplitDim.lean`). Log: `scratch/g0-dim/log.md`.

## 1. Result

**Both pieces are theorems, proved from Mathlib v4.35.0 alone: no leaf, no new hypothesis, no
`sorry`.** VERIFIED: `lake env lean scratch/g0-dim/Dim.lean` gives 0 errors, and `#print axioms`
gives `[propext, Classical.choice, Quot.sound]` for both:

```
theorem HSyn.G0Split.dimFinite : HSyn.G0Split.DimFinite
theorem HSyn.G0Split.dimBaseChange : HSyn.G0Split.DimBaseChange
```

The two statements are copied verbatim from `scratch/g0-split/part_split.lean` (VERIFIED by
`diff`), together with the objects they mention: `PkgI3.AbVar` and `PkgI3.AbVar.dim` (as in
`ZInQKernel/HDecomp/Objects.lean`), and `ZInQ.DefFaltings.AbVar`, `.baseChange`, `.dim` (as in
`Split.lean`'s section `ModelsSec`). The only difference is `noncomputable def` where the
source is a plain `def` inside a `noncomputable section`.

```
def DimFinite : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), ∃ n : ℕ, A.dim = (n : WithBot ℕ∞)
def DimBaseChange : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K),
    (A.baseChange L).dim = A.dim
```

So g0-split's main theorem now needs **eight** glue pieces instead of ten. The corollary is
`HSyn.glueOutputs_of_leaves_dim` in `part_dim.lean`: the same conclusion as
`HSyn.glueOutputs_of_leaves`, without the hypotheses `hDimF` and `hDim` (compile status in §4).

Neither piece is vacuous. `dim` is Mathlib's `topologicalKrullDim` of the underlying space, and
the proofs use only that `A.X.hom` is locally of finite type and quasi-compact (from `IsProper`)
and that `A.X.left` is nonempty (from the unit section `η`). The group structure, smoothness and
geometric integrality play no part. Both statements hold for every scheme of finite type over
a field, and that is what is proved.

## 2. The proof

All lemmas are in namespace `G0Dim` (compiled; Mathlib only).

| Lean name | statement | proof uses (Mathlib) |
|---|---|---|
| `ringKrullDim_eq_of_isIntegral_of_injective` | `A → B` injective and integral ⇒ `dim B = dim A` (STANDARD: Matsumura, *Commutative Ring Theory*, Thm 9.4 with incomparability; theorem number UNVERIFIED) | `Ideal.IsIntegral.under_lt_under` (incomparability), `Ideal.exists_ideal_over_prime_of_isIntegral` (lying over), `Ideal.exists_ltSeries_of_hasGoingUp` (going up) |
| `ringKrullDim_mvPolynomial_field` | `dim k[X₁…X_s] = s` | `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` |
| `ringKrullDim_tensor_field` | `R` of finite type over a field `K`, `L/K` any field extension ⇒ `dim (R ⊗_K L) = dim R` (Stacks 00P4, affine case) | Noether normalization `exists_finite_inj_algHom_of_fg` (Stacks 00OW): `K[X_s] → R` finite and injective. Its base change `K[X_s] ⊗ L → R ⊗ L` is finite (`RingHom.Finite.tensorProductMap`) and injective (`L` flat over `K`), and `K[X_s] ⊗ L ≅ L[X_s]` (`MvPolynomial.algebraTensorAlgEquiv`) |
| `ringKrullDim_le_of_finiteType` | `R` of finite type over a field ⇒ `dim R ≤ n` for some `n : ℕ` | Noether normalization |
| `topologicalKrullDim_eq_iSup_of_openEmbedding` | `dim X = ⨆ᵢ dim Yᵢ` for a cover of `X` by open embeddings `Yᵢ → X` | `IrreducibleCloseds.orderIsoOfIsOpenEmbedding`. A chain in `X` whose smallest member meets `Yᵢ` is a chain in `Yᵢ` |
| `dim_pullback_spec` | `m : Spec R → Spec K` loc. finite type ⇒ `dim (Spec R ×_K Spec L) = dim Spec R` | `Spec.preimage`, `HasRingHomProperty.Spec_iff`, `pullbackSpecIso` |
| `dim_baseChange` | `h : X → Spec K` locally of finite type ⇒ `dim (X ×_K Spec L) = dim X` (Stacks 00P4 globalized) | `X.affineCover`, its pullback along `pullback.fst` (`Cover.pullback₁`), `pullbackSymmetry`, `pullbackRightPullbackFstIso` |
| `dim_finite` | `h` locally of finite type and quasi-compact, `X` nonempty ⇒ `dim X = n`, `n : ℕ` | `QuasiCompact.compactSpace_of_compactSpace`, `OpenCover.finiteSubcover`, `krullDim_ne_bot_iff` |

`dimBaseChange` is `dim_baseChange` applied to `A.X.hom`: `(A.baseChange L).X.left` is
definitionally `pullback A.X.hom (Spec.map (algebraMap K L))`. `dimFinite` is `dim_finite`
applied to `A.X.hom`, with nonemptiness from `η[A.X].left` on a point of `Spec K`.

Nothing here is a leaf. All four inputs (lying over, going up, incomparability, Noether
normalization) are already in Mathlib.

## 3. By-products other tasks can use

- `ringKrullDim_eq_of_isIntegral_of_injective`. It is not in Mathlib v4.35.0 (VERIFIED by
  searching `Mathlib/RingTheory`). Any integral-extension dimension count needs it.
- `dim_baseChange` and `dim_finite` for arbitrary schemes over a field. They also give
  `dim (A_L) = dim A` for `PkgI3.AbVar.baseChange` (the same proof; `part_dim.lean` states it as
  `G0Dim.pkgI3_dim_baseChange` if the check in §4 passes).
- `topologicalKrullDim_eq_iSup_of_openEmbedding` (Stacks 0055-style; topological, no schemes).

## 4. What compiles, what remains

- VERIFIED: `scratch/g0-dim/Dim.lean`, 0 errors, standard axioms (run6, 34 s).
- Integration check (`SplitDim.lean` = g0-split's `Split.lean` + `part_dim.lean`): see the log for
  the outcome.
- Remains: nothing for these two pieces. For integration, append `part_dim.lean` to `Split.lean`
  (or insert it before `namespace HSyn`'s final theorems) and drop `dimFinite`, `dimBaseChange`
  from `G0Split.MissingPieces`.
