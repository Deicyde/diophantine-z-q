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
