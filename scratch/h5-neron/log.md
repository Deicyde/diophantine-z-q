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
