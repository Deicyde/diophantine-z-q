# g0-assemble results log

## 2026-11-13
- Copied scratch/h-decomposition/Leaves.lean to scratch/g0-assemble/Leaves.lean (byte-identical, `cmp`).
- Built the upstream helpers: `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (ok).
- parts/ (one file per wave-26 task, extracted by line range from the task's compiled file):
  05 bp-analytic Torus+QMLattice (kernel copy, for g0-thetapoint); 10 g0-dim part_dim; 20 g0-product §2-§5
  (G0Split. -> HSyn.G0Split. as in its mkcheck.sh); 30 g0-reverseisog SplitRev.lean tail (G0RevIsog only);
  40 g0-fibresimple tail; 50 g0-stablebc Main.part; 60 g0-heightadd (G0HeightAdd sections); 70 g0-mod-galois
  four parts; 80 g0-thetapoint part_theta (ThetaPt only); 90 the bundle GluePieces2 and the theorems.
