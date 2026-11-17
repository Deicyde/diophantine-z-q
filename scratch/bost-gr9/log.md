# bost-gr9 results log

## 2026-11-17 setup
- Base d67ea55f6 (= wip/leaf-fold33b top); origin/main is an ancestor (VERIFIED, git merge-base).
- Network: WebFetch of lmbp.uca.fr/~gaudron/art13.pdf and arxiv.org refused by sandbox (VERIFIED). GR14 §9 not
  read by this task; its content is taken from the locator audit (docs/research/locators.md row R21, AUDIT-READ):
  GR14 §9, proof of Lemme 9.1, p. 2098 uses h_F(A) >= -(3/2) dim A, referring to Bost and GR (CMH 2014) Cor. 8.4,
  with a normalization warning (content of the warning not recorded by the audit).
- Title per manuscript bibitem L11063-11066 and locators R19: "Polarisations et isogénies", Duke 163 (2014)
  2057-2108 (VERIFIED as recorded in the tree; not re-read in the print).

## Finding 1 (VERIFIED by arithmetic, compiled below)
- Consumer field ZInQ.R3Residual.BostLowerBoundAn: -(g/2)log(2π) <= x + (g/2)log π, i.e. x >= -(g/2)log(2π²)
  = -1.4913 g. GR14 §9's printed form: x >= -(3/2) g. The field is STRICTLY STRONGER than the cited print
  (1/2 log(2π²) < 3/2), so bostLowerBoundAn cannot be proved from a GR §9 leaf.
- The downstream need: R21_Bost (-(3/2) g <= stableFaltingsHeight), consumed via HeightSplit.r21_of_leaves' in
  heightRowsNo20_of8_hf_eb (EichlerBoundCopy.lean:470). TailY already has HeightSplit.GRBostBound (GR §9 form).
- Chain of the field in the bundles: bostLowerBoundAn (OpenResearchLeaves43CF..48, TailZ68-74) ->
  bostLowerBoundPrinted (TailZ74:990) -> HeightSplit.BostLowerBound (TailZ74:465, chevalley) -> R21
  (EichlerBoundCopy:482, OpenResearchLeaves8EB).

## Compile results (2026-11-17)
- `lake build ZInQKernel.OneProof.H.TailZ74 ZInQKernel.Contrib.OneProof.AnalyticStableHeight`: success (15369 jobs).
- `ZInQKernel/Contrib/OneProof/GaudronRemondSection9.lean`: compiles, no warnings (VERIFIED). Leaf
  GaudronRemondSec9LowerAn; normalization lemmas deligne_heightFormula_shift, deligne_bound_iff, bostAn_iff_faltings;
  half_log_two_pi_sq_lt, sec9_bound_lt_bost (old row strictly stronger); gaudronRemondSec9LowerAn_of_bostLowerBoundAn;
  sec9Printed_of_an(')/sec9An_of_printed; grBostBound_of_sec9Printed(_chevalley); r21_of_grBost('); r21_of_sec9An.
- Closure.lean: 114 affected structures; 110 decls to copy (TailZ74 33, TailZ69 1, EichlerBoundCopy 76).
- GR9Bypass.lean (gen_bypass.py, 4037 lines): compiles; sixContactMin_of_open67_gr9 axioms [propext,
  Classical.choice, Quot.sound]; field check: 29 vs 29 fields, only bostLowerBoundAn <-> gaudronRemondSec9LowerAn,
  no other type differs (VERIFIED). One fix needed: SGRFold sibling added12_of_open29_hf_pz qualified with _root_.
- `#discharges` (Main + Discharges + GaudronRemondSection9, 16216 jobs): 19 discharges, none by ZInQ.BostGR9
  (expected: leaf weaker than the field). Output in discharges.txt.
- autofold.json: mode "bypass" (not autofoldable), leaf row kind published, flag "pending reading: ...".
