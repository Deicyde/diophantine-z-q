# av-split results log

Base cba8157f (wip/av-split). Build artifacts: copied .lake/build from ~/dzq-wt/leaf-fold6 (same ZInQKernel sources as cba8157f; `git diff --stat cba8157f HEAD -- ZInQKernel` empty there); lake replays them.

## 03:20 T5Isog.lean (rows H-25, H-54)
- `lake env lean scratch/av-split/T5Isog.lean`: compiles, 56 s. VERIFIED.
- `AvSplit.torsionStructure_of_mumford : MumfordTorsionAlgClosed → PkgI2.TorsionStructure.{0}`; axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- `AvSplit.isogenyQuasiInverse_of_milne : MilneIsogenyQuasiInverse → WeilPairing.IsogenyQuasiInverse`; axioms standard. VERIFIED.
- Row H-54 text copied verbatim from scratch/g0-assemble2/parts/a35_g12det.lean L400-404 (diff with scratch/leaf-fold5/Leaves5.lean L49753-49755: identical). VERIFIED.
- Universe: TorsionStructure is universe-polymorphic (`K : Type u`); proved at u = 0 (AbVarBC infrastructure is at Type). Note for integration.

## 03:25 T35.lean (row H-38)
- compiles; `AvSplit.uniformizationExists_of_mumford : MumfordUniformizationC → ZInQ.LeafPush2.UniformizationExists`, axioms standard. VERIFIED.
- `AvSplit.mumford_of_uniformizationExists` (converse; the leaf is the row at K = ℂ, σ = id). VERIFIED.
- Proof: A_ℂ = A.baseChange ℂ via σ.toAlgebra; dim (AbVar.dim_baseChange); points via AbVarBC.bcPt; (bcPt p).left = p.left ≫ pullback.fst; cEvalAt via Scheme.Hom.comp_appLE.
