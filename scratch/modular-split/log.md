# modular-split results log

Build: `.lake/build/lib/lean/ZInQKernel` copied from ~/dzq-wt/leaf-fold8 (sources identical except
`Contrib/CloudW07JacobiansCurves/`, verified by `git diff --name-only`); `lake build
ZInQKernel.OneProof.H.TailT ZInQKernel.OneProof.H.LPrefix` exits 0 (VERIFIED, 11-14 11:3x).

## r15 `HDec.HSyn.DeligneSerreConseq` — DONE
- `scratch/modular-split/R15.lean`: `ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq`.
  Leaf: `ZInQ.Contrib.HodgeSplit.DSThm966` (Deligne–Serre 1974 Thm 4.1 / Diamond–Shurman Thm 9.6.6; already a
  published-form LEAF of the bundle, field `dsThm966`). Glue proved: `artinTransport_finite` (copy of hodge-split's
  `artinTransport_proof`, returning finite image), `attachedConj_proof` (T18+T19, kernel).
  Compile: `lake env lean scratch/modular-split/R15.lean` → axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
