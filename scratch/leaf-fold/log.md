# leaf-fold results log

- 05:52 start (fresh; no earlier log). Base 89a5e60e.
- Finding: Leaves.lean's namespaces (PkgI6, PkgI4, GlueConductor, GlueDescent, TSkolemKW,
  ZInQ.LeafPush2, ...) are the same as those of ZInQKernel/HDecomp (the kernel port), which every
  Contrib proof imports. Importing Contrib into Leaves.lean as is gives "already declared" clashes.
  Plan: wrap the whole body of Leaves.lean in `namespace HDec ... end HDec` (innermost-namespace
  name resolution keeps every reference inside the file pointing at the file's own copy); then
  the Contrib theorems (over root `PkgI6.…`) are converted to the file's `HDec.PkgI6.…` by
  definitional unfolding (`exact`), which is the required defeq check.
- 05:55 lake build of the needed Contrib modules started.
- 05:58 wrap.py, parts/t2.lean (T2Full proof), parts/tail.lean (repairs R14Det, R10 HT, G10 concrete; open bundles; #hdec_same checker), assemble.py written. First full compile pending the Contrib build.
- 06:04 first compile of the assembled file started; early errors: (1) Tau Ceti's root `IsArithFrobAt.eq_of_isUnramifiedAt` captures a dot-notation call (fix: call Mathlib's AlgHom lemma explicitly); (2) heartbeat timeouts (instance search in htSpace_cycRep_eq_bot; QML3.Iso.twist) — fix: global maxHeartbeats 1e6 / synthInstance 2e5 inside HDec.
- 06:14 first compile done (9m20s): errors only (a) heartbeat timeouts [fixed globally], (b) dot-notation capture [fixed], (c) T19 proof simp/rfl [now the kernel's identical proof, imported], (d) checker `count` typed as MessageData [fixed]. All new tail theorems compiled; t2/t15/t16a/t17/t18/t20/t21/t25/t30/t31 conversions by exact succeeded.
- 06:30 compile 2 aborted: global synthInstance 200000 made each failing search take minutes. Probe P1/P2: culprit is Tau Ceti's FinitePadicExtension instances (toAlgebra etc.); now `attribute [-instance]` inside HDec; probe shows the searches fast again. Compile 3 started.
- 06:39 compile 3 CLEAN: 0 errors, 10m13s, 210 #print axioms lines all standard. Installed as scratch/h-decomposition/Leaves.lean. #hdec_same: 5 exact matches; differences to analyse (proof-aux names, resp/GQp, HasNebentypus).
