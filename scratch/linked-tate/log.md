# linked-tate results log

## 2026-11-13
- Copied scratch/h-decomposition/Leaves.lean (pin-applied, commit base f90cf864) to scratch/linked-tate/Leaves.lean (byte-identical, `cmp`).
- Built upstream helpers: `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` + the three
  imports of imports_extra.txt (ok, 9171 jobs). First prefix run failed before that (`unknown module prefix 'ZInQ'`).
- parts/: verbatim copies of scratch/g0-assemble/parts/{70_galois,72_ladiccond,74_wp3,75_modfield,77_newform,87_afterg7}.lean
  (87 holds the target Props `ModelG3G6`, `LinkedTateData`, unchanged); 92_c10link.lean (kernel C10/Link.lean excerpts,
  verbatim); 93_g14.lean (scratch/g14-trace/part_g14.lean excerpts, verbatim); 95_linked.lean (new).
