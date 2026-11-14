# op-compact (fleet summary)

**Result.** The H chain (`ZInQKernel/OneProof/H/`) went from 8,224,119 to 4,195,116 bytes (−49 %) and from 80,137 to
79,208 lines. op-dedupe's 1,089 repeated alias opens (4.0 MB) are down to 79 lines (15 KB). The names now come from
57 `namespace HDec.T export _root_.T (...) end HDec.T` lines (69 KB), each written once in the chain; they re-create
the deleted copies' names `HDec.T.x` as aliases of the kernel's `T.x`.

**What builds.** `lake build +ZInQKernel.OneProof.Main` succeeds; `ZInQ.OneProof.frozenTarget` uses only
`[propext, Classical.choice, Quot.sound]`. Its `pp.all` type is unchanged (the diff of
`scratch/one-proof/frozenTarget_type_{before,after}.txt` is empty). All 8,202 constants of the OneProof modules
have the same type and value hashes before and after (`DumpCompact.lean`, `cmp_hashes.py`: 0 changed). No
declaration was touched.

**Pitfalls handled.**
- Aliases do not reach sub-names, so 648 child constants are aliased too.
- 3 children have kept HDec copies and are not aliased.
- 36 `ZInQ.Contrib.AbVarBC.{MulRigidity,G0FibreSimple}` names would have shadowed declared `HDec.MulRigidity.*`.
  An earlier version changed 8 TailE statements this way, and the hash check caught it. Those names keep merged
  alias opens, one line per namespace.
- Two `open Real ZInQ` lines in LPrefix are now `_root_.ZInQ`.

**What remains.** The 4.2 MB left is declarations and proofs, about 21 pull requests at 200 KB. The 71 kept alias
opens below `-- op-dedupe was:` could be folded the same way, but the saving would be about 15 KB. Generator:
`scratch/one-proof/compact.py` (on commit 39411fe1). Report: `docs/research/op-compact.md`; log:
`scratch/one-proof/log-compact.md`.
