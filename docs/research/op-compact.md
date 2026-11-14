# op-compact: the H chain without repeated alias opens

## Result

* **`ZInQKernel/OneProof/H/` shrinks from 8,224,119 to 4,195,116 bytes (−4,029,003, −49 %), 80,137 to 79,208
  lines.** The 1,089 alias opens `open _root_.Q (...) -- op-dedupe` (4.0 MB) are down to 79 lines (15 KB). The
  names are now provided by 57 `export` lines (69 KB), each written once in the chain.
* `lake build +ZInQKernel.OneProof.Main` succeeds. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
* **No statement changed, and no proof term either.** The `pp.all` type of `ZInQ.OneProof.frozenTarget` is the same
  before and after (`scratch/one-proof/frozenTarget_type_{before,after}.txt`, the diff is empty). A stronger check:
  `scratch/one-proof/DumpCompact.lean` hashes the type and the value of every constant declared in the
  `ZInQKernel.OneProof` modules (8,202 constants, `hashes_{before,after}.txt`). `cmp_hashes.py` finds the same 8,202
  names and **0 changed** hashes.
* No declaration was added, deleted or edited. The only changes are open and export lines, plus 12 `-- op-compact`
  comment lines that label the new blocks.

## Method

op-dedupe deleted 2,951 copies `HDec.Q.r` of kernel declarations `Q.r`. It made the remaining code see the kernel
names by adding `open _root_.Q (r ...)` after every `namespace`/`open` line inside `HDec`. Those lists repeat in
every section.

op-compact instead re-creates each deleted name as an **alias**:
`namespace HDec.T export _root_.T (rest ...) end HDec.T`. This makes `HDec.T.rest` an alias of the kernel's
`T.rest`, so a reference resolves exactly as it did to the deleted copy. Lean aliases persist through imports, so
each name is exported once, in the first module that used it (after that module's imports). The script is
`scratch/one-proof/compact.py`; it runs on the op-dedupe modules (commit 39411fe1) and reproduces the committed
files. Details:

1. **Sub-names.** `open X (a)` also reaches `X.a.b` (it matches by prefix), but an alias does not. So the
   non-internal constants below each alias target are aliased too: structure fields, constructors and `T.x.lemma`,
   648 in all, listed by `scratch/one-proof/Children.lean` → `export_children.txt`. Each one goes in the first module
   whose import closure contains the module that defines it.
2. **Kept copies.** No alias is made for a child `c` when `HDec.c` is still declared (3 cases, e.g. the kept copy
   `HDec.LeafQM.AV.QML3.goodReduction`). Aliasing it would be ambiguous.
3. **Shadowing.** An alias `HDec.q1…qk.r` must not shadow a declared `HDec.q1…qi.q(j+1)…qk.r` (i < j), because that
   is what `q(j+1)…qk.r` resolved to before. This was found by the hash check: 8 TailE statements changed in a first
   version. 36 names are affected: `ZInQ.Contrib.AbVarBC.G0FibreSimple.MulIsogeny` and 35
   `ZInQ.Contrib.AbVarBC.MulRigidity.*`. They are not exported. Their alias opens are kept, merged into one line per
   namespace after `namespace HDec`: 5 lines in TailE, and 1 each in TailF, TailH and TailJ.
4. **Explicit lists.** The 71 alias opens that replaced an original explicit-list open (below a `-- op-dedupe was:`
   comment) are kept unchanged.
5. **Namespace registration.** The `namespace HDec.T` command registers the namespace `HDec.T` at the top of the
   module. In LPrefix there were two `open Real ZInQ` lines that opened the root `ZInQ` because `HDec.ZInQ` was not
   yet a namespace at that point. They are now written `open Real _root_.ZInQ`, which is what they meant.

## Sizes per module

| module | bytes before | bytes after | lines before | lines after | alias opens before | after (opens / export lines) |
|---|---:|---:|---:|---:|---:|---:|
| LPrefix | 1,152,236 | 731,938 | 14,307 | 14,088 | 259 | 9 / 29 |
| TailA | 362,188 | 288,843 | 5,069 | 5,035 | 51 | 9 / 6 |
| TailB | 430,172 | 371,152 | 7,032 | 7,009 | 34 | 6 / 3 |
| TailC | 1,595,783 | 747,575 | 14,669 | 14,472 | 208 | 5 / 4 |
| TailD | 56,556 | 33,026 | 641 | 635 | 7 | 1 / 0 |
| LF2Stalks | 1,778 | 1,778 | 49 | 49 | 0 | 0 / 0 |
| LF2UnifRoot | 9,230 | 9,230 | 181 | 181 | 0 | 0 / 0 |
| LF2SmoothDim | 32,862 | 32,862 | 637 | 637 | 0 | 0 / 0 |
| LF2UnramConj | 11,677 | 11,677 | 207 | 207 | 0 | 0 / 0 |
| LF3Cot | 1,636 | 1,636 | 44 | 44 | 0 | 0 / 0 |
| TailE | 1,543,899 | 362,088 | 6,854 | 6,734 | 134 | 8 / 2 |
| TailF | 559,464 | 237,171 | 4,409 | 4,339 | 79 | 3 / 2 |
| TailG | 1,009,056 | 641,338 | 12,017 | 11,923 | 98 | 0 / 2 |
| TailH | 900,085 | 338,245 | 6,591 | 6,440 | 188 | 24 / 9 |
| TailI | 17,789 | 17,789 | 320 | 320 | 0 | 0 / 0 |
| LF4T5 | 77,762 | 77,762 | 1,644 | 1,644 | 0 | 0 / 0 |
| TailJ | 440,372 | 269,432 | 5,076 | 5,061 | 31 | 14 / 0 |
| TailK | 21,574 | 21,574 | 390 | 390 | 0 | 0 / 0 |
| **total** | **8,224,119** | **4,195,116** | **80,137** | **79,208** | **1089** | **79 / 57** |

The 4.2 MB that remains is declarations and proofs. At the 200 KB review cap, that is about 21 pull requests,
down from about 41.

## Notes

* The work was done for all modules in one pass instead of module by module, because the transform for module M
  depends on which names earlier modules have already exported. lake built the chain in import order. Builds 1–3
  failed: in LPrefix (sub-names, then children from modules not yet imported) and in TailC (a kept copy). Build 4
  succeeded but failed the hash check, and build 5 is clean (`scratch/one-proof/log-compact.md`).
* The export lines are long, up to 10 KB for `namespace HDec.ZInQ` in LPrefix. If a reviewer wants short
  lines, the names can be wrapped across lines with no other change.
