# fold-kleiman2 log

Base wip/leaf-fold33b 75d94fe7 (TailZ67, `sixContactMin_of_open60`; render_open on base: 39 open, H strictest 11/23 on 34).

1. Merged origin/wip/kleiman-section2 7591fc3b (with kleiman-section's history; adds only files: Contrib
   KleimanPicZero954.lean, KleimanPicZeroProperQuot.lean, docs, scratch). Hygiene: 5 scratch files redeclaring
   HDec.HSyn bundles renamed .lean.txt (kleiman-section/{TailZ56,FrozenCheck,AutofoldDry},
   kleiman-section2/{TailZ56,FoldCheck}); no host paths found; no vendored LICENSE/NOTICE involved.
2. Readers of the field on the current top (VERIFIED, grep of ZInQKernel/): `l.kleimanPicZeroProper` is read only
   (a) in the generation conversion OpenAddedLeaves25 -> 24 -> 23 -> 22PZ (`picZeroAbVar0_of_leaves`) and
   (b) in `openResearchLeaves35_of_OpenResearchLeaves36_eb` (EichlerBoundCopy) via
   `HodgeTateFromPairing.hodgeTateDecompAbVar_of_open`, which also uses it only through `picZeroAbVar0_of_leaves`.
   So the chain reads the field only as `PicZeroChar0.PicZeroAbVar0` = `KleimanSection2.picZeroAbVar0_of_954`.
3. Generator scratch/fold-kleiman2/gen/gen.py (copy reroute; walks the chain from Main's top call). Output
   ZInQKernel/OneProof/H/TailZ68.lean: `OpenAddedLeaves26 = {picRepresentableAbVar, kleimanPicZeroProper954}`,
   `openAddedLeaves22PZ_of_OpenAddedLeaves26`, `t09SymmIsogenyExists0_of_open_k954`,
   `hodgeTateDecompAbVar_of_open_k954`, 14 copies `X_k954` (sixContactMin_of_open60 ... 48_eb and
   openResearchLeaves35_of_OpenResearchLeaves36_eb), `sixContactMin_of_open48_eb_k954` entering
   `sixContactMin_of_open45_pz_eb`; top `sixContactMin_of_open61`. Main.lean patched (import TailZ68, l retyped,
   top call open61).
