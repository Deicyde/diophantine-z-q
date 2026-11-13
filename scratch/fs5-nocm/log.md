# fs5-nocm results log

- 05:22 base 2dd83306; merged origin/wip/qm-pin, origin/wip/mobius-glue (g0-fibresimple already in base).
- FS5 source: scratch/g0-fibresimple/FibreSimple.lean L20190-20206 (`HSyn.G0Split.FibreComTrivial`).
  Its names resolve to kernel copies: `R1fpProps`, `R2fpProps`, `QML3`, `M3`, `com`, `Qbar` (LeafQM.AV,
  ZInQKernel/HDecomp/QM/*), `contactSet` (ZInQ, Hypotheses/Height.lean), `Jmap` (ZInQ.JHeight).
- Repaired R1 text: scratch/qm-pin/QM-Leaves-full.patch L63-70 (R1fpProps := old 4 clauses ∧ R1famProps ∧ R1univProps).
- lake build ZInQKernel.HDecomp.QM.Leaves, Repo.PRArith, Hypotheses.JHeight: OK (VERIFIED).
