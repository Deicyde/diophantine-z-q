# leaf-fold results log

- 05:52 start (fresh; no earlier log). Base 89a5e60e.
- Finding: Leaves.lean's namespaces (PkgI6, PkgI4, GlueConductor, GlueDescent, TSkolemKW,
  ZInQ.LeafPush2, ...) are the same as those of ZInQKernel/HDecomp (the kernel port), which every
  Contrib proof imports. Importing Contrib into Leaves.lean as is gives "already declared" clashes.
  Plan: wrap the whole body of Leaves.lean in `namespace HDec ... end HDec` (innermost-namespace
  name resolution keeps every reference inside the file pointing at the file's own copy); then
  the Contrib theorems (over root `PkgI6.…`) are converted to the file's `HDec.PkgI6.…` by
  definitional unfolding (`exact`), which is the required defeq check.
- 06:0x lake build of the needed Contrib modules started.
- 06:25 wrap.py, parts/t2.lean (T2Full proof), parts/tail.lean (repairs R14Det, R10 HT, G10 concrete; open bundles; #hdec_same checker), assemble.py written. First full compile pending the Contrib build.
