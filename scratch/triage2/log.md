# triage2 results log (base 9a100aa7)

## Setup
- lean/.lake missing in worktree -> probes run with scratch/triage2/run.sh (LEAN_PATH + ~/dzq/lean/.lake, same lean/ZInQ tree 02e27597).
- Trace.lean: worklist trace of field projections through bundle converters in the closure of ZInQ.OneProof.frozenTarget.

## Agent reports (SPECULATIVE until re-checked)
- agent-H (R5 heights): no removal; all four feed heightRowsNo20_of8 (TailZ4:153) -> R18/R19/R21/R22; GR reverse-isogeny use needs existence only (bypass via milneIsogenyQuasiInverse, weakening only).
- agent-G (R7): no removal; all uses on the u-family QM surface A (p=5 for HT/dR; l=3,5 for dsThm965, r9a, r9b surjective half).
- agent-R (R1 semistable): r6 uses only QM surfaces over number fields; SS1/SS2/SS3 used for all height-row A incl. J1(N)_L.
  Candidate removal: semistablePersistsSHcp via (b) Raynaud-at-every-L'⊇K'3K'4 + SemistableLocalGlobal (bypass fold) or
  (a') derive SemistablePersistsDVRnf from sga7_IX_3_3 (3.3 second assertion ⇒ first). To verify.
## Run 2 (05:32)
- Trace.lean launched (background); agents X (BG, DelX6), W (GR x2), T (hCM, h33), Y (DelY3 narrow + GLUE notes) launched.
- VERIFIED (read): SS3 consumer r20Lower_of_leaves' TailY.lean:666-683 applies hSS3 only along L1 ⊆ L (SS1 witness).
- VERIFIED (read): ss1_ss3_of14 TailZ23.lean:767 is the only use of r.semistablePersistsSHcp; SS1 (semistableReductionThm_of_leaves_nf
  TailZ23:509) and SS3 (semistablePersists_final_nf) both take SemistablePersistsDVRnf (TailZ23:425); persistsNF_of_general
  gives it from SemistablePersistsDVR (TailZ7:711).
- VERIFIED (read): identityComponentBaseChangeDVRRange_of (TailZ19:1595, proved from SGA3_VIB_3_10, SGA7_IX_3_3,
  GeomConnOfRationalPoint) gives j : (U ×_O O') → 𝒩' open-immersion hom for U = 𝒩⁰ (range = idCompSet), any field K.
  IsSemistable = HasSemiAbelianIdentityComponent of geomSpecialFibre (TailZ7:197, def TailY:79: exists open connected
  subgroup U with flat surj hom onto AbVar B, kernel split torus in functor of points).
- CANDIDATE A (SPECULATIVE plan): SemistablePersistsDVR from identityComponentBaseChangeDVRRange_of + fibre transport
  (U_s ⊆ 𝒩⁰_{κ̄} by connectedness, base change κ̄→κ̄', GeomConnOfRationalPoint for connectedness). Removes
  semistablePersistsSHcp with no new field (uses sga3_VIB_3_10, sga7_IX_3_3_SH+pair, geomConnOfRationalPoint, all on chain).
- agent-T (hCM, h33): both keep (T4). VERIFIED by me: cmModuli_of (RingClassLattice.lean:1128) is the hCM consumer; the
  chain Main.lean:67 → shimuraReciprocityModFn_of_printed (:3352) → _of_t5''/_of_t5'/_of_t5 (:2762/2754/2741).
  MainTheoremCMj is itself a def (TYZChain/ModFn.lean:105), not proved. Uses span all squarefree n ≡ 5,7 mod 8: no finite
  specialization. Optional T1 hygiene narrowings only (agent-T.md).
- agent-W (GR x2): both read only in nocm_on_witness (TailC.lean:1371-1456, VERIFIED by me: h5 at :1390, hC at :1403).
  Prop56X6 enters only via r5count (TailZ27:110 → TailZ9:96 → TailK:294). Bypass (T3, SPECULATIVE): identify R ∈ {ℤ[i], ℤ[√−6]}
  by elementary norm-form arguments, contradiction via HasCM4/HasCM24 + J(u) ∉ {0,−16/27}; drops r5count. X6Ab: T4 keep.
- agent-X: deligneComponentsX6PrintedAb (and geomConnOfAlgClosure) only feed R1pi0Props, last conjunct of R1R2fpRep
  (LPrefix:5223); R1R2fp_of_rep (LPrefix:5229) discards it (VERIFIED by me, read). Other readers to be checked by probe
  Pi0Use.lean. babaGranathRationalAb ⇐ ElkiesEquationsX6Ab (derived) ∧ CMPairsExist (SPECULATIVE plan via
  shimuraMainThmIDeligneY3AbU ModuliAtUnits + HomLatticeCorr + descend_main copy).
- NOTE geomConnOfAlgClosure is held (claims.tsv: cloud batch 2): a prune would make that task moot; flag to the lead.
- Trace.lean killed after 25 min (no output; per-seed scan too slow); replaced by targeted binder-use probe Pi0Use.lean.
- agent-Y: deligneComponentsY3PrintedAb used only as TSHecke.Y3Connected (TailG:8352: ∃ Y Φ, R1fpProps ∧ ConnectedSpace Y.left),
  single real use TailK:317. Narrow route (T3, SPECULATIVE) from shimuraMainThmIDeligneY3AbU + (𝒪/3)^× decide at K=ℚ(i).
  shimuraIntegralModelRep: weakest use VertUnramWitness E p (p>324); LEAF by reading Buzzard 1997 §§1-4 (UNVERIFIED).
- PROBE Pi0Use.lean (compiled, 1m20, out3): in the closure of frozenTarget, the only constants with a binder of exact type
  HDec.LeafAdopt.R1pi0Props that USE it are the producers r1r2fpRep_of, canonicalCoarseX6_of, coarseX6OfFine_of; all
  destructurers (R1R2fp_of_rep, r5fp_of_rep, r1rec_of_rep, pairsLift_of_rep, pairsLift_of_canonical) discard it; the other
  mentioning constants (descend_main, canonicalModelY3_of_coarse) discard by pattern (read). VERIFIED: R1pi0Props is
  never consumed on the live path. (Watched-name bug in run 1: LeafAdopt vs HDec.LeafAdopt; run 2 counted conjunction binders.)
- VERIFIED (read): r1r2fpRep_of_printed (TailZ20:1855) takes the base witness from geomConnX6_of hD hE; a prune must take
  the witness (R1fpProps ∧ X6Props) from another leaf, e.g. hG (GonzalezRotgerX6, :1858).
## Pass 2
- ProbeA.lean COMPILED: #check list for task 2; fold check `ss1_ss3_of_persistsT2` + example over (r,t,l) at the leaf-fold14
  generation: SS1 ∧ SS3 from `target sga3_VIB_3_10 sga7_IX_3_3 geomConnOfRationalPoint` with no semistablePersistsSHcp. VERIFIED.
- ProbeB.lean COMPILED (main theorem): `babaGranathRationalAb_of_elkiesT2 : ElkiesEquationsX6Ab → CMPairsExistT2 →
  BabaGranathRationalAb` proved in full (t₄=1, t₃=∞, t₂₄=0). VERIFIED. (#check of RayClassCFT names failed only because
  TailZ22 does not import RayClassShimura.)
- ProbeC.lean COMPILED: R1R2fpRepW, R1R2fp_of_repW (proof unchanged), geomConnX6W_of_gr. Rethreading scope: 41 live constants
  mention R1R2fpRep in their type (6 bundle structures r1r2/r1b fields: OpenResearchLeaves2/5/7/8/9, ResearchLeaves3; ~25
  theorems); CanonicalCoarseX6 8, GeomConnX6 4, CoarseX6OfFine 3; GeomConnOfAlgClosure 18 (bundle fields + 6 theorems).
- ProbeA extended: SemiAbelianBaseChangeAlgClosedT2 (the one new transport lemma) elaborates; #check hasSemiAbelian_pullback (TailZ14:1006), semiAbelianFieldIsoInvariant, hasSemiAbelian_of_iso, idComp_baseChange OK. COMPILED.
- agent-CM: ℂ-side CM already proved (cmFixedHasCM_of TailJ:1270; cm4/cm3/cm24_exists TailJ:255-275); descend_main uses
  hTD/hRep only for the level structure / R1fp naturality.
- ProbeD.lean COMPILED (0 errors): cmComplexT2 (HasCM4/3/24 objects over ℂ from shimuraMainThmIDeligneY3AbU +
  uniformizationLeafAll + gagaMorphism); pairOfT2 (truncated descend_main, no TorsionDescends, no R1R2fpRep);
  cmPairsExistT2_of; and `babaGranathRationalAb_of_open28T2 (n : OpenResearchLeaves21) (t : OpenTextbookLeaves11)
  (l : OpenAddedLeaves17) : BabaGranathRationalAb` — axioms [propext, Classical.choice, Quot.sound]. VERIFIED:
  the field babaGranathRationalAb is derivable from the other top-bundle fields (elkiesX6StarPrinted,
  shimuraMainThmIDeligneY3AbU, uniformizationLeafAll, gagaMorphism, shimuraTaniyamaQbar). Task 3 → T1 (fold only).
- ClauseUse.lean (compiled; errors only in an unused renamed helper): every other conjunct of R1R2fpRep/R1R2fp (R1heckeProps, X6Surj, R5ptProps, R1recProps, CMExists, R2X6Props(Iff)) has a real consumer (e.g. nocm_on_witness, heckeNoVertRam_of_witness): no further clause prune.
