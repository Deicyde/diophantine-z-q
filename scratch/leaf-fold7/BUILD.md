# leaf-fold7: how the new modules were made and checked

Sources → modules (all generated from the split tasks' committed files; `verbatim_check7.py` checks the result):

| module | source | change |
|---|---|---|
| TailP | scratch/av-glue/Combined.lean | `#print` lines and the GENERATED banner dropped; banner added |
| TailQ | scratch/av-split/AvSplitAll.lean | `#print` dropped; the MulRigidity copy (identical to kernel `Contrib/FrobChain/Rigidity.lean`, diffed) replaced by that import |
| TailR | scratch/curve-split/{CurveBij,CurvesGSplit,X0Split}.lean | imports merged; each file in a `section`/`end`; `#print` dropped |
| TailS, TailT | scratch/hodge-split/HodgeSplit.lean | cut before §16 (lines 6-2063, 2064-end); TailT reopens the file header (options, namespace, opens, `variable (p)`) |
| TailU | scratch/qm-split/{ClassNumberOne,YuLeaf,QMAut,STQM,ThetaSplit,ModuliSplit}.lean | `import TailK` → `import ZInQKernel.OneProof.H.TailO`; each file in a `section`/`end`; trailing `#print`/`example` dropped |
| TailV | new | hodge-split transports (`HodgeLF7`) |
| TailW | scratch/mcr-glue/MCRGlue{1,2,3}.lean.part; scratch/curve-split/ShimuraGR.lean l. 131-174 | inside `namespace HDec`; `#print` dropped; `CurveSplit` → `CurveSplitGR` |
| TailX | new | bundles `Open*7`, maps to leaf-fold6's bundles, `sixContactMin_of_open7` |

Checks (one Lean process at a time):

```
lake build +ZInQKernel.OneProof.Main                       # exit 0, frozenTarget axioms standard
lake env lean scratch/leaf-fold7/DumpCompact.lean          # writes scratch/leaf-fold7/hashes.txt
python3 scratch/leaf-fold7/cmp_hashes.py                   # hashes_before.txt vs hashes_after.txt
lake env lean scratch/leaf-fold7/Check7.lean               # conclusion, closure, field heads
python3 scratch/leaf-fold7/verbatim_check7.py              # modules vs sources
```

`test/` holds the probe files used to find the R10 transport (R10T*.lean); they are not part of the build.
