# st-qbar — fleet summary

**Proved (VERIFIED, compiled, axioms `[propext, Classical.choice, Quot.sound]`):** `STQM` outright, in
`ZInQKernel/Contrib/OneProof/STQM.lean` (namespace `GapST`, imports only `ZInQKernel.OneProof.H.TailO`):

```lean
theorem GapST.stQM_of (hRep : HDec.LeafAdopt.R1R2fpRep) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : _root_.PkgI2.TorsionStructure.{0})
    (hU : _root_.ZInQ.LeafPush2.UniformizationExists) (hC : _root_.ZInQ.HomUnify.HomLatticeCorr) :
    HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
```
Hypotheses: fields `r1r2`, `y3Connected`; `ALFixedPoints` = chain theorem `(qmRows_of7 t l).2.1`; T5, T35,
`HomLatticeCorr` = `AvSplit.Final.h25/h38/h69` of `mumfordTorsionAlgClosed`, `uniformizationLeafAll`,
`gagaMorphism`. No new leaf. Also `GapST.cmDescends_of` (`CMDescends`), `GapST.cm_point` (a CM `ℂ`-point of `Y₃`
comes from `Y₃(ℚ̄)`), `GapST.twist_of_cm` (converse of `ALFixedPoints` over `ℂ`: CM by `ℤ[i]`/`ℤ[ζ₃]`/`ℤ[√−6]` ⇒
`(A,ι) ≅ (A, ι∘rep k)`; possibly useful to cm-stab), `GapST.exists_level3`.

**Method:** `ψ = ι(w)c/n` ((i,1+φ,2), (j,2φ−1,3), (ij,φ,6)) is an Atkin–Lehner-type automorphism (integrality by
`A[p] ≅ 𝒪/p𝒪` + `decide` mod p, division via T35 + HomLatticeCorr); the CM point of `Y₃(ℂ)` is fixed by
`g_α ≫ g_u` (R1hecke), which moves a non-CM `ℚ̄`-point (ALFixedPoints); `Y₃` integral, so a fixed generic point
would force `g_α ≫ g_u = 𝟙` (`ext_of_isDominant`); hence the point is closed and comes from `ℚ̄`.

**#discharges:** 63 open hypotheses, 5 discharge one — none ours (`STQM` is not a field; the field
`shimuraTaniyamaQbar` is more general). So a manual fold, not autofold.

**Manual fold:** the only consumer of `shimuraTaniyamaQbar` is TailX.lean L261 (`stQM := stQM_lf7 l.shimuraTaniyamaQbar`);
replacement `stQM := _root_.GapST.stQM_of r.r1r2 l.y3Connected (qmRows_of7 t l).2.1 (_root_.AvSplit.Final.h25
t.mumfordTorsionAlgClosed) (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
(_root_.AvSplit.Final.h69 t.uniformizationLeafAll t.gagaMorphism)` (compiled, `scratch/st-qbar/FoldCheck.lean`).
Forwarding lines and the full bypass are in docs/research/st-qbar.md §3; `scratch/st-qbar/BypassFold.lean`
compiles `frozenTarget_S` with `OpenAddedLeaves17S` (no `shimuraTaniyamaQbar`), standard axioms.
Counts (kinds.tsv H rows): 56 → 55 fields; strict 46/10 → 45/10; strictest 45/11 → 44/11.

**Remains:** the fold itself (integration lead). Nothing unchecked.
