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
