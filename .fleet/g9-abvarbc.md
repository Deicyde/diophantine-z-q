# g9-abvarbc — fleet summary

**Main result: `G9Bridge.AbVarBaseChange` is proved outright from Mathlib** (no leaf, no hypothesis):
`ZInQ.Contrib.AbVarBC.abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange`
(`ZInQKernel/Contrib/AbVarBC/Main.lean`). With g9-derham's `g9Glue_of_abVarBaseChange` this gives
`g9Glue_of_r10Weights : G9Bridge.R10Weights → G0Galois.G9Glue`, so G9 rests on `R10Weights` alone.
No statement change was needed.

By-products, also outright: mul-rigidity's leaf `KerUnitOpen` (`kerUnitOpen`) and
g0-fibresimple's `MulIsogeny` (`mulIsogeny`: `[n]` finite surjective, char 0), proved with tangent
vectors as `K[ε]`-points (the group law makes their derivations additive, so `d[n] = n`), with no
stalks of fibre products. Torsion descent and `T_ℓ(A) ≅ T_ℓ(A_L)` (`tateBC_bijective`).

Reusable API over the kernel's `PkgI3.AbVar` (12 new files in `ZInQKernel/Contrib/AbVarBC/`):
`PkgI3.AbVar.dim_baseChange`, `dim_finite`, `bcPt`, `extPt_injective`, `ptBC`, `tateBC`,
`tateBC_galT`, `vBC`, `vBC_galRep`, `TorsionDescends`, `exists_lift_of_isFinite`,
`torsionDescends_of_isFinite`, `Tangent.ptRing`, `Tangent.D_mul`, `Tangent.ks_isOpenImmersion`,
`AbVarBaseChangeK` / `abVarBaseChangeK`.

Consumers discharged: hodge-lattice `DimBaseChange` (`dimBaseChange`; `hodgeLatticeTheorem_of_tangent'`
etc.), e1-sub `bcT_bijective` without `hdim` and, in char 0, without T26 (`bcT_bijective_charZero`),
g4-weilres `hdim` (`dim_overPullback`), and alternative routes `abVarBaseChange_of_tateModuleFree`,
`…_of_mulIsogeny`, `…_of_kerUnitOpen`, `…_of_cotangent`.

Compiles: `lake build ZInQKernel.Contrib.AbVarBC.{Main,Consumers,E1SubBC}` (VERIFIED); 41 theorems
checked with `#print axioms`, all `[propext, Classical.choice, Quot.sound]`
(`scratch/g9-abvarbc/axioms-output.txt`). No sorry, no axiom, no heartbeat options.

Remains: nothing for this target. For G9 only `R10Weights` (g9-derham F1). Report:
`docs/research/g9-abvarbc.md`; log: `scratch/g9-abvarbc/log.md`.
