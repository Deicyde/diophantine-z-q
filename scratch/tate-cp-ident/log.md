# tate-cp-ident log
- base f3add5ae8029bd36f55ccb84a4317bc0a3a5121a confirmed
- Step 0: lake build +Rows +AbVarBC.Main +LF4T5: ok, 1m31s (Rows rebuilt 77s)
- Steps 1-2 (cpAlgF, cpAlgF_algebraMap rfl, fbarToCp, fbarToCp_embF, fbarToCp_galF, cpGalF, cpGalF_apply rfl, coe_oAct_gfToGqp rfl): lake env lean ok 6.6s
- rule-5 #synth check (scratch, uncommitted section): Algebra ℚ_[p] ℂ_[p] -> UniformSpace.Completion.algebra (PadicAlgCl p) ℚ_[p]; Algebra (fieldF p F) ℂ_[p] -> (fieldF p F).instAlgebraSubtypeMem. Both pre-existing; local instance low kept.
- lake build +...CpPoints: ok 10s
- Steps 3-6 (ptFbarToCp, _injective, _galAct, _torsion via T5Torsion.exists_extPt_eq + mulIsogeny, _tate_bijective via tate_map_bijective_of_torsion, _tate_galT, colmezTateFbarCp, colmezVpFbarCp): first lake env lean ok 9.5s (2 linter warnings: haveI, deprecated induction_on -> fixed)
- no copy bridging needed: row I3.AbVar terms accepted at DeRhamPrint.toKer / PkgI3.Tate.map types as-is
- lake build +...CpPoints: ok 11.9s, no warnings from CpPoints
- ProofCheck.lean (uncommitted): lake env lean ok 6.3s; both theorems: [propext, Classical.choice, Quot.sound]
