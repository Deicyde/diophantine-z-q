# theta-direct (fleet report)

**Proved, no hypotheses** (ZInQKernel/Contrib/OneProof/ThetaDirect.lean + helpers in ThetaDirect/; axioms
[propext, Classical.choice, Quot.sound], VERIFIED by `#print axioms`):
* `HDec.ThetaDirect.thetaRatiosAtQM_proof : HDec.HSyn.G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM` — theta-split's use
  form of the GLUE field `thetaRatiosAlgebraic` (algebraic theta ratios where `j_θ(Ω(τ)) ∈ ℚ∖0`), statement copied
  verbatim from theta-fold's TailK;
* `thetaRatiosAtQM_of_qmHauptmodul : PkgI1.QMHauptmodul → ThetaRatiosAtQM` (theta-fold's consumer binder);
* `thetaPointOfFibre_of_qmPeriod : FibreQMPeriod → ThetaPointOfFibre` (drop-in at TailK's `gluePieces_of_open4`).

No Lin–Yang, no `QMHauptmodul`, and no leaf at all — not even `IgusaThetaExpressions`: Igusa's theta expressions
`ψ₆`, `χ₁₂` are shown modular at `M4`, `M6` directly from gt-theta's squared theta laws (a signed permutation of their
terms, checked exactly in sympy and in Lean). Then the kernel's proved valence formula for `Γ*` gives
`ψ₆Σθ⁸ = c₁∏θ²` and `(Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)²` on `Ω(ℍ)`, with `c_i` algebraic from the CM points `√2+i`, `τ₂₄`
(cm24-value, period-glue), and igusa-alg's `IgusaAlg 3..9` finish.

**#discharges** (scratch/theta-direct/discharges.txt): 62 open hypotheses, 2804 theorems checked, 7 discharge one —
none for `thetaRatiosAlgebraic`, as expected (use form, not the universal field).

**Fold (manual, for the integration lead):** −1 GLUE, −1 field, no new hypothesis. theta-fold's plumbing (`hθ` through
`gluePieces_of_open4`, `_open4` … `_open29`) and prune (the field in `OpenAddedLeaves4…17`, three dead readers), with
Main supplying `hθ := HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul`; also X0ModuliUsed.lean's three
alternative tops; generated as scratch/theta-direct/fold/fold.patch by make_fold.py. **The patched tree builds**
(Main + Discharges, 13006 jobs): frozenTarget axioms standard, `#discharges` 62 → 61 open hypotheses. Every consumer
with file:line is in docs/research/theta-direct.md §3.

**Remains:** applying the fold (docs/kinds/STATUS regeneration, PruneScan); deleting the UseForm.lean copy at fold time. Merge of wip/theta-fold
conflicted and was aborted; definitions copied instead.
