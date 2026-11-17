# gr56-prove results log

Base 43513d87 (leaf-fold25). Target: research field `gonzalezRotgerProp56X6` (`GRCountX6.GonzalezRotgerProp56X6`).

## Findings
- VERIFIED (scratch/gr56-prove/Reach.lean, reach.txt; closure of `ZInQ.OneProof.frozenTarget`, 97682 constants):
  the only live consumer of the count (`R5fpCount`, reached from the field through
  `gonzalezRotgerCountX6Ab_of_printed` (TailZ27) and `ShimuraSplit.r5fpCount_of_points` (TailZ8/9)) is
  `HDec.FS5NoCM.nocm_on_witness` (TailC L1371), via `fibreComTrivialOwn_of`, `fibreComTrivialFull_of`,
  `fibreComTrivialFull_of_leaves'`, `fibreComTrivialFull_of_leaves''` (TailC), called from TailK L294
  (`gluePieces_of_open4`, `r.r5count`). LPrefix's `subsingleton_of_bundle` (pi0 route) is not live.
- VERIFIED (reading TailC L1371-1452): `nocm_on_witness` uses the count only as an upper bound
  (`#CM(R) ≤ 2` against four distinct CM points), for arbitrary `R`.
- Assessment: the field (exact count for every order of conductor prime to 6) needs (a) Eichler's
  optimal-embedding count (local quaternion orders at 2, 3; not in Mathlib) and (b) the existence of QM
  surfaces over ℚ̄ with prescribed CM (Shimura; no kernel input). Neither is in reach; plan: prove the
  injection CM(R) ↪ optimal embeddings mod 𝒪^× from the textbook fields (lattice model), giving the
  upper bound from `GRCountX6.EichlerOptEmbCount6`, and reroute the single consumer.

## Compile log
- Probe1.lean: names checked (VERIFIED).
- GR56Lattice.lean §1-§2 (LatData, exists_latData, ρn, realize, qmIso_of_scalar): compiles after cancel fix.
- GR56Lattice.lean §3-§10 compile (VERIFIED, `lake env lean`, 0 errors); `#print axioms` of
  `GR56.exists_injective_optEmb`, `GR56.card_cmSet_le`, `GR56.emb_opt`, `GR56.qmIso_descend`:
  [propext, Classical.choice, Quot.sound].
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GR56Lattice`:
  OK (12995 jobs). `#discharges` (scratch/gr56-prove/discharges.txt): 63 open hypotheses, 1899 theorems checked,
  7 discharge one, none from GR56 (expected: R5fpCountLe is weaker than the field; manual fold).

## Statements proved (GR56Lattice.lean)
- `GR56.exists_injective_optEmb hU hG hM k hk R hR hc : ∃ F : CMSet R → Quot (GRCountX6.ConjRel R), Injective F`
- `GR56.card_cmSet_le … (hfin : Finite (Quot (ConjRel R))) : Finite (CMSet R) ∧ card (CMSet R) ≤ card (Quot …)`
- `GR56.R5fpCountLe` (def), `GR56.r5fpCountLe_of_r5fpCount : R5fpCount → R5fpCountLe`,
  `GR56.r5fpCountLe_of_eichler : EichlerOptEmbCount6 → hU → hG → hM → R5fpCountLe`
- `HDec.FS5NoCM.nocm_on_witness_le`, `fibreComTrivialOwn_of_le`, `fibreComTrivialFull_of_le`,
  `fibreComTrivialFull_of_leaves'_le`, `fibreComTrivialFull_of_leaves''_le` (consumer chain with R5fpCountLe).
- §8b-§8f compile (VERIFIED): `conj_of_iso`, `qmIsoBC`, `exists_eigvec`, `latData_of_torus`, `com_equiv_of_eig`,
  `cmMap`, `cmMap_injective`, `cmMap_surjective`, `cmPointsOptEmb6_of`, `r5fpCount_of_leaves`,
  `gonzalezRotgerProp56X6_of_leaves`; `#print axioms`: standard three.
- `#discharges` rerun (VERIFIED, discharges.txt): `DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by
  GR56.gonzalezRotgerProp56X6_of_leaves still assumes [GRCountX6.EichlerOptEmbCount6, GR56.QMTorusAbelian,
  GR56.CMPairDescendsQbar, UniformizationLeafAll, GAGAMorphism, MumfordTorsionAlgClosed]`; 63 open, 1956 checked, 8 discharge one.
- autofold.json (3 new leaves) `--dry-run`: strict 46/10 on 56 -> 48/10 on 58; strictest 45/11 -> 47/11 (VERIFIED);
  generated module (FoldCheck.lean, dry-run output minus line 1) compiles, `sixContactMin_of_open30` standard axioms.
- §8g (VERIFIED, compiles): `exists_alpha` (two embeddings Qbar -> C differ by an endomorphism of Qbar),
  `bc_comp_iso` (via `G0StableBC.exists_pbPaste`; a direct proof hit a kernel deterministic timeout),
  `cmPairDescendsQbar_of_st : ShimuraTaniyamaQbar → CMPairDescendsQbar` (uses `QMSplitSTQM.embed_Ed`, `irr_d`,
  `Ed_finrank`), `gonzalezRotgerProp56X6_of_st`, `cmPointsOptEmb6_of_st`. `CMPairDescendsQbar` restated in the
  STQM d-form (CM element with negative integer square) before any fold.
- `#discharges` rerun: field discharged by `GR56.gonzalezRotgerProp56X6_of_st` still assuming
  [EichlerOptEmbCount6, QMTorusAbelian, ShimuraTaniyamaQbar (existing added-bundle LEAF), the three textbook fields];
  63 open, 1973 checked, 9 discharge one.
- autofold.json now: leaves `eichlerOptEmbCount6`, `qmTorusAbelian`; proof uses `{l}.shimuraTaniyamaQbar`.
  `--dry-run`: strict 46/10 on 56 -> 47/10 on 57; strictest 45/11 -> 46/11. FoldCheck.lean compiles, standard axioms.
- `qmTorusAbelian_of_main : ShimuraMainThmIDeligneY3AbU → QMTorusAbelian` (VERIFIED, compiles): the research
  field's moduli clause `ModuliAtUnits` at u = 1 is exactly QMTorusAbelian. `gonzalezRotgerProp56X6_of_main`,
  `cmPointsOptEmb6_of_main` (no new leaf besides Eichler).
- autofold.json (main variant): only new leaf `eichlerOptEmbCount6`; proof
  `GR56.gonzalezRotgerProp56X6_of_main {n}.eichlerOptEmbCount6 {n}.shimuraMainThmIDeligneY3AbU {l}.shimuraTaniyamaQbar {t}...`.
  `--dry-run`: strict 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11 (VERIFIED). FoldCheck.lean compiles,
  `sixContactMin_of_open30` standard axioms. Alternative spec autofold-alt-torus.json (leaf qmTorusAbelian instead
  of the composite field): 46/10 -> 47/10.
- `#discharges`: 63 open, 1976 checked, 10 discharge one; GR56 discharges the field by `_of_main`, `_of_st`,
  `_of_leaves`.
