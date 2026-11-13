# g0-x1belyi: `X1BelyiOnModel` is proved

Task g0-x1belyi, 2026-11-13. The piece is missing piece 3 of `scratch/g0-split/Split.lean`,
`HSyn.G0Split.X1BelyiOnModel` (glue E2, the Belyi half). Lean: `scratch/g0-x1belyi/`. Results
log: `scratch/g0-x1belyi/log.md`.

## Main result

The piece is now a Lean theorem. Its statement is copied verbatim and not changed.

```lean
theorem G0X1Belyi.x1BelyiOnModel_of_belyiX1 (hB : LeafModCurves.BelyiX1) :
    HSyn.G0Split.X1BelyiOnModel
theorem G0X1Belyi.x1BelyiOnModel_of_leaves (hT : X1Belyi.TorsionStructure)
    (hG : X1Belyi.GoodReductionUnramified) : HSyn.G0Split.X1BelyiOnModel
```

The first theorem is pure glue: it transports the statement along the isomorphism
`ℚ(X) ≅ K_N`. The second adds x1-belyi's proof `X1Belyi.belyiX1_of_leaves`
(`docs/research/x1-belyi.md`). So `X1BelyiOnModel` follows from two published theorems, and the
rest of the proof is in Lean:

| Name | Kind | Statement and source |
|---|---|---|
| `X1Belyi.TorsionStructure` (T1) | **leaf** | `E[N](K) ≅ ℤ/N × ℤ/N` for an elliptic curve over an algebraically closed field `K` of characteristic 0, `N ≥ 1`. Silverman, *AEC*, Cor. III.6.4(b) (UNVERIFIED number). STANDARD. |
| `X1Belyi.GoodReductionUnramified` (T2) | **leaf** | Function-field form of Néron–Ogg–Shafarevich: good reduction of `E/k(T)` at an irreducible `p ∈ k[T]` (char `k` = 0) ⇒ `k(T)(x(P))` is unramified over `p` for every torsion point `P`. Serre–Tate, Ann. of Math. 88 (1968), Thm 1, with Serre, *Local Fields* I §7 (UNVERIFIED numbers). STANDARD. |
| `LeafModCurves.BelyiX1` | glue, proved by x1-belyi | `j/1728` is a Belyi function on `K_N`, and `[K_N : ℚ(j)] ≤ N²` |
| `X1BelyiOnModel` | glue, **proved here** | transport of `BelyiX1` to the model `X` given by `IsJ1` |

Status: VERIFIED. Two checks compiled, each with no errors and no `sorry`, and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for every theorem below.

1. `scratch/g0-x1belyi/X1OnModel.lean`, 562 lines, about 30 s. It imports
   `ZInQKernel.HDecomp.ModCurves.Glue` and is assembled by `build.sh`.
2. `scratch/g0-x1belyi/Integ.lean`, about 3 min. This is the integration check, assembled by
   `build_integ.sh`; the file is not committed, so regenerate it with the script. It consists of
   g0-split's `Split.lean` plus this proof, so the proof is checked against Split.lean's own copies
   of the definitions. In it:

```lean
theorem HSyn.sixContactMin_of_leaves_x1 (r : ResearchLeaves) (t : TextbookLeaves)
    (hR18 : R18_JavanpeykarConcrete) (hR22 : R22_PazukiConcrete)
    (hT : X1Belyi.TorsionStructure) (hG : X1Belyi.GoodReductionUnramified)
    (hDimF : DimFinite) (hDim : DimBaseChange) (hSimp : FibreSimple)
    (hAdd : HeightAdditivity) (hBC : StableHeightBaseChange) (hProdE : ProductExists)
    (hRev : ReverseIsogeny) (hThetaPt : ThetaPointOfFibre) (hMod : ModularConstituent) :
    ZInQ.SixContactMin
```

This is g0-split's `sixContactMin_of_leaves` with the hypothesis `X1BelyiOnModel` replaced by the
two leaves T1 and T2. Nine glue pieces of g0-split remain.

## The proof (`scratch/g0-x1belyi/part_onmodel.lean`)

`IsJ1 N J` supplies the following data: a model `X`, a base point `P₀`, a map `aj` with
`IsJacobian X P₀ J aj`, the facts `IsCurve X` and `IsIntegral X.left`, a point `P` of exact order
`N`, and a ring isomorphism `e : ℚ(X) ≃+* K_N`. The proof keeps `X, P₀, aj` and takes
`t = e⁻¹(j/1728)`. Then it does the following.

* **ℚ-linearity.** Any ring isomorphism of `ℚ`-algebras is `ℚ`-linear (`RingEquiv.toRatAlgEquiv`).
  So `e` is an isomorphism of `ℚ`-algebras for `ffAlgebra X` on `ℚ(X)`, whatever `ℚ`-algebra
  instance `K_N` carries.
* **The Belyi property transports** along `k`-algebra isomorphisms (`isBelyiFunction_of_algEquiv`).
  A valuation subring `w` of `ℚ(X)` corresponds to `w.comap e⁻¹` on `K_N`, and nonunits correspond
  through `ValuationSubring.mem_nonunits_iff_or` (`mem_nonunits_comap`). Transcendence transports
  through `IsAlgebraic.algHom`, and `aeval` through `Polynomial.aeval_algHom_apply`.
* **The degree transports** (`finrank_adjoin_of_algEquiv`). `e` maps `ℚ(t)` onto `ℚ(e t)`
  (`IntermediateField.adjoin_map`), and `Algebra.finrank_eq_of_equiv_equiv` gives
  `[ℚ(X) : ℚ(t)] = [K_N : ℚ(j/1728)]`.
* **`ℚ(j/1728) = ℚ(j)` inside `K_N`** (`mem_adjoin_image`, `finrank_adjoin_image_X_div`). The image
  of every `p(j)/q(j)` lies in `ℚ(t')`: `j = 1728·t'`, and the proof uses polynomial induction with
  `RatFunc.num_div_denom`. So `[K_N : ℚ(t')] = [K_N : ℚ(j)]`, which is at most `N²` by `BelyiX1`.
* **`0 < d`** (`finrank_fieldX1_pos`). `K_N = ℚ(j)(x(P))` with `x(P)` in an algebraic closure, so
  `K_N` is finite over `ℚ(j)`.

## Faithfulness of the copy

* `X1BelyiOnModel`, `ffStructMap` and `ffAlgebra` are copied verbatim from `Split.lean`
  (checked by `diff`).
* The other declarations the piece depends on are imported in `X1OnModel.lean` from
  `ZInQKernel/HDecomp/Objects.lean` and `ModCurves/{Defs,Leaves}.lean`: `PkgI3.AbVar`,
  `AbVar.dim`, `Qj`, `Ej`, `Kbar`, `EjBar`, `xCoord`, `fieldX1`, `IsCurve`, `SpecQ`, `IsX1Model`,
  `RatPt`, `IsJacobian`, `IsJ1`, `IsBelyiFunction` and `BelyiX1`. Their text is identical to the
  Split.lean copies (VERIFIED by `scratch/g0-x1belyi/defdiff.py`).
* `Integ.lean` removes any doubt about the copies, because there the proof elaborates against
  Split.lean itself.

The piece is neither false nor vacuous. Its hypothesis `IsJ1 N J` is satisfiable given
`X1ModelExists` (proved by x1-belyi from leaves M1-M3 and T1) and `JacobianExists` (T33), via
`LeafModCurves.exists_J1`. Its conclusion is the substantive Belyi statement that `javanpeykarJ1`
feeds to R18.

## What remains (not done)

* **Bridging to the bundles.** T1 and T2 are not fields of `ResearchLeaves` or `TextbookLeaves`.
  The bundles contain the abelian-variety versions:
  * `TextbookLeaves.t5 : PkgI2.TorsionStructure` (Mumford, `A[n] ≅ (ℤ/n)^{2g}`);
  * `ResearchLeaves.r7a : PkgI2.NeronOggShafarevich`.

  Both are stated for group objects in `Over (Spec K)`, while T1 and T2 are stated for points of
  Mathlib Weierstrass curves. Deriving T1 and T2 from t5 and r7a would need the projective
  Weierstrass curve as an abelian-variety group scheme, with its `K̄`-points identified with
  `W.toAffine.Point`. Mathlib 4.35 does not have this, and it was not attempted.

  Until this bridge is built, the decomposition gains two leaves, T1 and T2. Both are textbook
  statements specialized to elliptic curves (VERIFIED, read in `Split.lean` L1548, L10884 and
  `scratch/x1-belyi/X1Belyi.lean` L75, L92).
* g0-split's docstring of `X1BelyiOnModel` says "the transport is not done here". That is now done
  in `scratch/g0-x1belyi/`. Split.lean was not edited.
