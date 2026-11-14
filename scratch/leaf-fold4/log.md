# leaf-fold4 results log

## 17:45 start (fresh; no earlier log)
- Base 8ec80711. Merged origin/wip/leaf-fold3 (f7951690), period-glue (7e1531df), zariski-conn (3802f2bc),
  t5-torsion (58ac8d0b), homlattice (89a1fc02), kerwild-fix (f596943a), frobchain-contrib (f4bf0b72),
  hecke-rest (6c2c1d76; its .fleet note dropped in the merge). spread-out (aa304ed7) was already in the base.
  origin/wip/vert-witness and origin/wip/t40-clash do not exist yet (17:50).
- No leaf-fold3 oleans exist on this host: the whole chain is rebuilt. `lake build` of the kernel modules
  imported by the chain plus Contrib SpreadOut, ZariskiConn, FrobChain started 17:46.
- Copied leaf-fold3's build into scratch/leaf-fold4/ (ctail.sh path changed).
- mk_propts.py re-run on the merged hecke-rest/HeckeRestAll.lean: c80 gains hecke-rest's curve proofs
  (`HeckeRestCurve.chartProper`, `chartQuasiFinite_of_proper`, `curveChartInf`), and
  `HeckeRestAll.coverModelOfHecke_of_heckeRest` no longer takes ChartProper/ChartQuasiFinite.
  d90_fold3.lean: the one call adjusted (hP, hQ unused). assemble.sh: only TailG and TailI differ from leaf-fold3.
