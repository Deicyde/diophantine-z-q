# leaf-fold7 results log

## 2026-11-14 06:40 PST start
- Base debc37b4 (wip/w56). OneProof top: HDec.HSyn.sixContactMin_of_open6 (68 fields: 26 + 21 + 20 + 1).
- Read reports: av-glue, curve-split, av-split, height-split, hodge-split, qm-split, mcr-glue, frontier r3.
- Plan (strict decision rule): side modules (kernel imports only) for av-glue, av-split, curve-split, hodge-split;
  qm-split pieces over the chain (import TailO); final bundle module importing TailO and the side modules.
- 06:45 started `lake build +ZInQKernel.OneProof.Main` (TailL-TailO and ~36 kernel modules were out of date).
- 07:01 base build done (`lake build +ZInQKernel.OneProof.Main`, exit 0; the chain LPrefix..TailO was rebuilt since
  kernel modules it imports were out of date, ~15 min). DumpCompact (copy in scratch/leaf-fold7/) before any change:
  8594 OneProof constants hashed -> hashes_before.txt; frozenTarget axioms standard.
