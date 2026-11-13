# h5-neron results log

Start 2026-11-12 22:53 PST. Base 01267822. Build of ZInQKernel.HDecomp.Faltings.Leaves: OK.

## Plan (decided 23:00)
- Nonzero abelian varieties cannot be constructed in Mathlib v4.35 (Objects.lean `AbVar.zero`
  docstring): StableHeightFinite for elliptic curves is NOT provable now (needs AV7 + AN3).
- Provable now: (A) Néron mapping-property glue (lift, uniqueness, products);
  (B) the zero abelian variety: Néron model, metrized model, stable height = 0;
  (C) reduction of "stable height = Néron height over a semistable field" to stated Props.

## Part A: scratch/h5-neron/Neron.lean — COMPILED 23:10 (no errors; axioms propext, Classical.choice, Quot.sound)
- `NeronProp j P N A e` (abstract Néron mapping property along `j : S' ⟶ S`, test class `P`).
- `NeronProp.lift` (∃! extension), `NeronProp.uniqueIso` (two Néron models iso compatibly with gen),
  `tensorGen`, `NeronProp.tensor` (product of Néron models is a Néron model of the product).
- `GroupModel.isNeronModel_iff` (project's IsNeronModel = NeronProp with smooth tests),
  `GroupModel.IsNeronModel.lift` (∃! 𝒢 → 𝒩 compatible with gen), `.uniqueIso`.

## Part B: scratch/h5-neron/ZeroAV.lean — COMPILED 23:12 (axioms propext, Classical.choice, Quot.sound)
- `modelHeight_dim_zero`: every `MetrizedModel A L 0` (any A) has modelHeight 0
  (lattice = span{1⊗1}, coeff(1⊗1) = jacDet = det of 0×0 = 1, covol of the lattice in ℂ⁰ = 1).
- `pts_subsingleton`: a group model of `AbVar.zero K` has one ℂ-point at each τ
  (adjunction Over.map ⊣ Over.pullback, generic fibre ≅ 𝟙).
- `no_metrized_succ`: no metrized model of `AbVar.zero K` with g ≥ 1 (kernel = ℂ^g not discrete).
- `trivModel`, `trivModel_isNeronModel` (Spec 𝓞_L is a Néron model of (Spec K)_L), `trivMetrized`.
- `stableFaltingsHeight_zero : stableFaltingsHeight (AbVar.zero K) = 0` for every number field K.
- 23:20 added, COMPILED: `metrizedOf` (every group model of the zero AV is metrizable in g = 0),
  `groupModel_height_zero` (every group model of it has height 0), `neronModelMinimal_zero`,
  `stableHeightFinite_zero`, `isIsogeny_id_zero`, `isogDeg_zero_le_one`, `one_le_grKappa`,
  `R19_zero`, `R20_zero`, `R21_zero` (the three leaves hold for A = B = zero, all hypotheses
  satisfiable: x = 0, the identity is an isogeny).

## Part C: scratch/h5-neron/Reduction.lean — COMPILED 23:12 (axioms propext, Classical.choice, Quot.sound)
- defs `IsBaseChangeOf 𝒢' 𝒢` (group-object iso to 𝒢 ×_{𝓞L} 𝓞L'), `IsOpenSubgroupModel 𝒰 𝒢`.
- leaves (Props): `NeronModelExists` (BLR 1.4/3, UNVERIFIED), `SemistableNeronIdentityComponent`
  (SGA 7 IX 3.6 + 3.3, UNVERIFIED).
- glue (Props, unproved): `ModelHeightBaseChange`, `GroupModelBaseChangeExists`, `OpenSubgroupHeight`
  (+ existing `NeronModelMinimal`).
- proved: `compositum` (two number fields over K in a common number field, inside AlgebraicClosure K);
  `stableFaltingsHeight_eq_neron` (∃ L₀, Néron 𝒩₀ over L₀ with stableFaltingsHeight A = 𝒩₀.height).
- FINDING: the Néron model does not commute with base change even for semistable A (component groups
  grow: Tate curves; STANDARD); only the identity component does. So the leaf is phrased via a common
  open subgroup, and `OpenSubgroupHeight` is needed. def-faltings/rv-blueprints said "base change of
  semistable Néron models (SGA 7 IX 3.3)" without this caveat.

## Part A addendum (Neron.lean) — COMPILED 23:14
- `NeronProp.of_iso` (transport along isos), `IsProductAbVar C A B`, `bcProd`, `IsProductModel`,
  `isNeronModel_of_isProductModel` (product of Néron group models is Néron).
- glue Props: `ProductGroupModelExists`, `ProductModelHeight` (≤ direction).
- `stableFaltingsHeight_add_le`: h(A) + h(B) ≤ h(C) for C ≅ A × B, from NeronModelExists,
  NeronModelMinimal, ProductGroupModelExists, ProductModelHeight.
- FINDING: the E4 direction of additivity needs NO semistable reduction (rv-blueprints F1 said it
  needs H5 = Néron + semistable base change): comparing over each L separately suffices.

## Combined file scratch/h5-neron/H5Neron.lean — COMPILED (no errors; all 24 #print axioms
## list only propext, Classical.choice, Quot.sound)
Parts A + B + C plus part D:
- `isMonHom_of_iso_unit`, `neron_zero_iso_unit` (a Néron model of the zero AV is ≅ 𝟙, via uniqueIso),
  `neronModelExists_zero` (N1 for zero AV), `semistableNeronIdentityComponent_zero` (N2 for zero AV,
  L₀ = K), `glue_zero` (ModelHeightBaseChange / OpenSubgroupHeight / ProductModelHeight shapes hold
  for zero AV group models since all heights are 0).
- stableFaltingsHeight_eq_neron_all (stable height = Néron height over L₀ and over every L' ⊇ L₀): COMPILED in H5Neron.lean and Reduction.lean

## Part E: scratch/h5-neron/ProductModel.lean — COMPILED 23:31; merged into H5Neron.lean (27 #print axioms,
## all [propext, Classical.choice, Quot.sound]; 0 errors)
- `isMonHom_prodComparisonIso` (prodComparison of Over.pullback is a monoid morphism).
- `productGroupModelExists : ProductGroupModelExists` — glue P1 PROVED.
- `stableFaltingsHeight_add_le'`: h(A)+h(B) ≤ h(C) from NeronModelExists, NeronModelMinimal,
  ProductModelHeight only.
- Independent model review (subagent, read-only) of H5Neron.lean: no PROBLEM; N1, N2 judged
  consequences of BLR 1.4/3 and SGA 7 IX 3.6+3.3; all glue judged true; two docstring
  inaccuracies (OpenSubgroupHeight "identity on A_L(ℂ)"; eq_neron_all "so A_{L₀} semistable") FIXED.

## Part F: scratch/h5-neron/BaseChange.lean — PARTIAL (compiles; the main theorem is NOT proved)
- COMPILED: `pbCompHom/pbCompInv/pbEqIso/pbEq`, `isMonHom_pbCompHom`, `isMonHom_pbCompInv` (components of
  `Over.pullbackComp` are monoid morphisms, via `Functor.mapMonNatIso` + `Functor.mapMonCompIso`),
  `isMonHom_pbEq`, `square1` (jL' ≫ φ = ψ ≫ jL), `square2`, `bcGen` (generic-fibre iso of a base change).
- FAILED: `bcGen_isMonHom` / `groupModelBaseChangeExists`: elaborator accepts (~50 s), kernel reports
  "(kernel) deterministic timeout" (also with maxHeartbeats 2000000: > 10 min, stopped). Proof kept as a
  comment. Glue H4b stays UNPROVED.
- Diagnosis: `convert this using 1` leaves a goal identical up to hidden instance arguments, so the mismatch is in instance terms (MonObj/monoidal-functor instance paths), not in the morphism.
