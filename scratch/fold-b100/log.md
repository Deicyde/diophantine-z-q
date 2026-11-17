# fold-b100 log

Base: wip/leaf-fold33b 1cd875a13 (top `sixContactMin_of_open64`, `OpenResearchLeaves45`, `OpenTextbookLeaves17`,
`OpenAddedLeaves26`). Before step 1: render_open count H 5/29 on 34 (strict LEAF/GLUE), from the base commit message.

## Step 1: coeff-field-tc

* Merged coeff-field-tc 135186536 (proof commits only, not its fold commit b19d5e47, which was made on e1b31749):
  `ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFiniteProof.lean` (`eigenformCoeffFieldFinite_proof :
  DSCoeffExt.EigenformCoeffFieldFinite`), vendored Tau Ceti files, ThirdParty/TauCeti/NOTICE, docs/research/coeff-field-tc.md,
  scratch/coeff-field-tc/ (no build logs, no host paths, no .lean scratch).
* Readers on the live path (VERIFIED by grep and by the generator's assert, 4 readings):
  `CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan n.heckePrimeIntegralToRational` in
  EichlerBoundCopy `openResearchLeaves31_of_OpenResearchLeaves32_eb` (eigenformCoeffFieldFinite),
  `openResearchLeaves32_of_OpenResearchLeaves33_eb` (r17), TailZ65 `openResearchLeaves39_of_OpenResearchLeaves40`
  (r11r12, eigenformHTNew); TailZ70's conversion makes `gamma1IntegralSpan` from `gamma1IntegralBasis`.
* Generator `scratch/fold-b100/gen_coeff_fold.py` (adapted from coeff-field-tc's gen_fold.py, kept as
  gen_fold_coeff_orig.py.txt): copies the 14 research generations of the live path (32EB-38EB of EichlerBoundCopy,
  36EB's live conversion from TailZ69 (k954), 39 of TailZ63, 40-45 of TailZ65-71) with suffix CF
  (45 -> `OpenResearchLeaves46`), conversions `_cf`, fields deleted, readings -> `_root_.eigenformCoeffFieldFinite_proof`.
  Output `ZInQKernel/OneProof/H/TailZ72.lean` (1199 lines), top `sixContactMin_of_open65 (r : OpenResearchLeaves46)
  (t : OpenTextbookLeaves17) (l : OpenAddedLeaves26)` := `sixContactMin_of_open48_eb_k954 (...) t16 l`.
* Main.lean: imports TailZ72, `r : OpenResearchLeaves46`, `sixContactMin_of_open65`; doc paragraph.
* kinds.tsv: rows `gamma1IntegralBasis`, `heckePrimeIntegralToRational` dropped. claims.tsv: no rows for them (an outside
  contributor's claim of heckePrimeIntegralToRational is on the GitHub claims issue: not touched, see report).
