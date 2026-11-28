# HeightModelM: the Néron-model height is Gaudron–Rémond's semi-abelian-model height

Item M of the Gaudron–Rémond statement checks. An adversarial reading of the rows
`gaudronRemondSec9LowerAnSS` (GR1, Comment. Math. Helv. 89 (2014), Cor. 8.4) and
`gaudronRemondThm14AnSS` (GR2, Duke Math. J. 163 (2014), Thm 1.4) passed on fidelity and failed on
one point: there was no Lean identification between the height computed on the full semistable
Néron model (`ZInQ.SemistabAssembly.IsAnStableHeightSS`) and the height GR1 §2.3 defines on a
semi-abelian model. This directory supplies it, from one printed leaf, EGA IV₃ (9.7.7).

## What is proved

* `isGR1StableHeightOriginal_of_isAnStableHeightSS (hE : EGAIV_9_7_7_OL) :
  IsAnStableHeightSS A x → IsGR1StableHeightOriginal A x`. The semi-abelian model is `𝒩⁰`, the
  open union of the identity components of the fibres of the semistable Néron model `𝒩`, over the
  same ring of integers. The section is pulled back along `𝒩⁰ → 𝒩`, and the index and
  archimedean norms are unchanged.
* `GaudronRemondSec9LowerGR1` is GR1 Cor. 8.4 as printed (Bost's strength) over the GR1 height.
  `GaudronRemondSec9LowerGR1Weak` is the same at the current field's strength, `-(3/2) g`.
  `gaudronRemondSec9LowerGR1Weak_of_GR1` proves the print implies the weak form (the weakening
  GR make on p. 352), and `gaudronRemondSec9LowerAnSS_of_GR1Weak : EGAIV_9_7_7_OL →
  GaudronRemondSec9LowerGR1Weak → ZInQ.BostGR9.GaudronRemondSec9LowerAnSS` gives the old row
  (the field until item-m-fold). The fold carries the weak form, so the restatement is not stronger
  than the old field.
* `gaudronRemondThm14Printed_of_GR1 : EGAIV_9_7_7_OL → GaudronRemondThm14GR1 →
  ZInQ.GR14Printed.GaudronRemondThm14Printed` gives the old Duke row
  (`gaudronRemondThm14AnSS_of_GR1` gives the older `AnSS` form too).
* `frozenTargetM`: `ZInQ.OneProof.frozenTarget` with the research bundle `OpenResearchLeaves79M`.
  Its proof term is `Main`'s before item-m-fold (top `sixContactMin_of_open100`), with `r` passed
  through `openResearchLeaves79_of_M` and nothing else changed.
* **Direction.** The new rows imply the old fields (proved). The converse, from the GR1 height to
  the Néron-model height (a semi-abelian model's height is computed on some semistable Néron
  model), is not proved in the tree, so the GR1 rows are not shown equivalent to the old fields.

Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` (`Check.lean`). No `sorry`,
no `axiom`, no build-time code.

## Files

* `EGA977.lean`: the leaf `EGAIV_9_7_7_OL`, EGA IV₃ (9.7.7)(ii) at `Spec 𝓞_L`, and the glue
  `genericConnectedFibresOL_of_ega`. A locally constructible subset of `Spec 𝓞_L` that contains
  the generic point has finite complement, so a smooth model with geometrically connected generic
  fibre has only finitely many disconnected fibres. Imports Mathlib only.
* `OpenIdComp.lean`: `isOpen_idCompSet_of_ega`, `𝒢⁰` is open for every group model `𝒢` over
  `𝓞_L`. The generic fibre is geometrically connected (Stacks 04KV, proved in the tree). Also
  `SGA3_VIB_3_10_NeronOLPrinted` and its proofs.
* `SemiAbelianModel.lean`: `IsSemiAbelianModel`, GR1's "modèle semi-abélien" (every special
  fibre connected and an extension of an abelian variety by a torus, over `k(𝔭)` and `k̄(𝔭)`), and
  `exists_semiAbelianModel` (the open `𝒩⁰` is a semi-abelian group model with an open immersion
  homomorphism onto `𝒩⁰`).
* `MetricTransport.lean`: along an open immersion homomorphism `𝒢₀ → 𝒩` of group models, the
  Hodge lattice and the index (`secIndex_hodgeMap`), the analytic topology (a homeomorphism),
  holomorphic charts in both directions, the measures `(i/2)^g η̃ ∧ η̄̃`, hence
  `isAnMetricSq_hodgeMap`.
* `GR1Height.lean`: `IsGR1StableHeightOriginal` (GR1 §2.3, original normalization) and the
  identification.
* `Rows.lean`: the printed rows `GaudronRemondSec9LowerGR1` (and its weak form) and
  `GaudronRemondThm14GR1`, and their implications to the old rows.
* `FoldCheck.lean`: `OpenResearchLeaves79M`, `openResearchLeaves79_of_M`, `frozenTargetM`. It
  imports `TailZ107` (the chain top when it was written) and the headline modules, not `Main`.
* `Check.lean`: `#print axioms` for the theorems above.

## Reading notes

Pages were read from numdam page images. The files are the IHÉS PDFs, with SHA-256 checksums:
EGA IV₃ `f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e`, EGA III₁
`3ed59fe81da07f1ab685ddc54a93128a364419d4ddafbc7affcd8abc8b401605` and EGA IV₂
`c3e960aa1c5c37046e8892d8a3cac098e2738164136b5cdaa5d5d893f89931da`. These are AI readings and
clear no flag.

* **EGA IV₃ (9.7.7)**, Publ. Math. IHÉS 28 (1966), p. 79: "Soit `f : X → S` un morphisme de
  présentation finie, et soit `E` l'ensemble des `s ∈ S` pour lesquels `X_s` a l'une des
  propriétés suivantes : être : (i) géométriquement irréductible ; (ii) géométriquement connexe ;
  (iii) géométriquement réduit ; (iv) géométriquement intègre. Alors `E` est localement
  constructible dans `S`."
* **Constructible and locally constructible**: EGA 0_III (9.1.1)–(9.1.3) and (9.1.11), Publ. Math.
  IHÉS 11 (1961), pp. 12–14. A constructible set lies in the smallest family that contains the
  retrocompact opens and is stable under finite intersection and complement. A locally
  constructible set is one where each point has an open neighbourhood `V` with `T ∩ V`
  constructible in `V`. These are Mathlib's `Topology.IsConstructible` (the Boolean subalgebra
  generated by the retrocompact opens) and `Topology.IsLocallyConstructible`.
* **Geometrically connected**: EGA IV₂ (4.5.2) with (4.5.1), Publ. Math. IHÉS 24 (1965), p. 61.
  The number of connected components of `X ⊗_k Ω` is `≤ 1`, or equivalently `X ⊗_k K` is
  connected for every extension `K` of `k`. The empty scheme counts. `IsGeomConnFibre` is that
  condition on the fibre: every base change of `X_s` to a field over `k(s)` is preconnected.
* **Lean form of the leaf**: (ii) at `S = Spec 𝓞_L`, `L` a number field, for `X` smooth,
  quasi-compact and quasi-separated over `S`. Smooth implies locally of finite presentation, so
  this is a direct instance of the print.
* **GR1 §2.3**, p. 351: the height is defined on "un modèle semi-abélien" `𝒜` over `𝒪_K` for some
  finite `K` over which `A` has semi-abelian reduction, with "Cette définition est indépendante
  des choix de `K` et de `𝒜`". P. 352: `h_F(A) = h(A) - (g/2) log π`. `IsGR1StableHeightOriginal`
  computes `h_F` on one semi-abelian group model, with the metric of the existing rows
  (`IsAnMetricSq`, `2^{-g} ∫ |η ∧ η̄|`). The printed rows write `h(A)` as `x + (g/2) log π`.
* `IsSemiAbelianModel` does not ask for commutativity of `𝒜`. Each fibre (an extension of an
  abelian variety by a torus) and the generic fibre are commutative, so this changes nothing
  mathematically. It is noted because GR1 does not spell out the definition.

## Count and fold plan

The fold landed as item-m-fold: `OpenResearchLeaves80` in `ZInQKernel/OneProof/H/TailZ108.lean` (the
fields of `OpenResearchLeaves79M`), `openResearchLeaves79_of_OpenResearchLeaves80` (the terms of
`openResearchLeaves79_of_M`) and the top `sixContactMin_of_open101`, 21 → 22. Ratings as of
2026-11-28 (`docs/one-proof/kinds.tsv`): `egaIV_9_7_7_OL` LEAF; `gaudronRemondSec9LowerGR1Weak`
consequence, GLUE; `gaudronRemondThm14GR1` published, LEAF strict and GLUE strictest, read in Duke's
version of record. The plan as written follows.

The fold is a copy reroute with no change to existing declarations.

1. The new research bundle is `OpenResearchLeaves79M`: `OpenResearchLeaves79` with
   `gaudronRemondSec9LowerAnSS` and `gaudronRemondThm14Printed` replaced by
   `gaudronRemondSec9LowerGR1Weak`, `gaudronRemondThm14GR1` and `egaIV_9_7_7_OL`, every other
   field kept (`bergerSurveyF` included). Bundle 16 → 17 fields, H 18 → 19, total 21 → 22.
2. `Main` changes only `r`'s type. It goes through `openResearchLeaves79_of_M`, as
   `frozenTargetM` does here.
3. Rating, pending the statement checks:
   * `egaIV_9_7_7_OL` (read from the numdam journal scans) and the Sec9 rows (read from the EMS
     journal file of GR1; the bundle carries the weak form, the full Cor. 8.4 is the read print)
     are LEAF candidates.
   * `gaudronRemondThm14GR1` was read from the authors' copy of the Duke paper with Duke
     pagination. Following the precedent of `panThm104F`, it stays GLUE until the Duke journal
     text is checked.
   * The old forms stay reachable through `gaudronRemondSec9LowerAnSS_of_GR1Weak` and
     `gaudronRemondThm14Printed_of_GR1`.
