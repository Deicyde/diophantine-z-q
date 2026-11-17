# pb-fix results log

## 2026-11-15 22:36 start
- Base c1636db9 (pb-bypass); fast-forwarded to origin/wip/pb-sanity 9dbaabbd3 (pb-sanity reported: B_cris ≠ 0, t not
  nilpotent, etc., in ZInQKernel/Contrib/OneProof/PanBergerSanity.lean). VERIFIED (git merge --ff-only).
- Build tree: copied ~/dzq-wt/pb-sanity/.lake/build (same commit 9dbaabbd3) into .lake/build (old one moved to .lake/build.old).
- Plan: new file ZInQKernel/Contrib/OneProof/PanBergerFix.lean:
  * K0 K := ℚ_p(prime-to-p roots of unity in K) (max. absolutely unramified subextension).
  * IsSemistableOverT: tensor form (B_st ⊗ V^*)^{G_K}, normalized by finrank K0 (explicit [K_0:ℚ_p]).
  * BergerPrintedT := BergerDR LocalIsPstT.
  * PanPrintedT: ∀ ι_p : ℚ̄_p ≃+* ℂ, tr ρ(σ_arith) = ψ(σ) ι_p^{-1}(a_q(g)) (no algebraicity in the leaf).
  * glue: PanFor LocalIsPstT from PanPrintedT + DSThm965 + DSThm966 (r14Det_of_printed) + Steinitz.

## 2026-11-15 23:00 PanBergerFix.lean compiles
- `lake build +ZInQKernel.Contrib.OneProof.PanBergerFix`: success, no warnings in the file (VERIFIED).
  Fixes needed: IsTorsionFree/FaithfulSMul ℚ_p ℚ̄_p instances supplied by hand (typeclass search timed out
  even at 400000 heartbeats); `Module.Free`/`Module.Finite` of `Fin n → E` supplied by `haveI`.
- Axioms (scratch/pb-fix/axioms-output.txt): panBerger_of_printedT, panFor_of_printedT, coeff_mem_range,
  exists_complex_equiv, isSemistableOverT_iff, localIsPst_iff_T, finrank_K0_pos, finrank_K0_bot: standard (VERIFIED).
- #discharges (scratch/pb-fix/discharges-output.txt): `DISCHARGES [OpenResearchLeaves22.r11r12] by
  HDec.PkgI4.PanBergerSplit.panBerger_of_printedT; still assumes: PanPrintedT, BergerPrintedT, DSThm965, DSThm966`;
  totals 63 open hypotheses, 1950 theorems checked, 9 discharge one (VERIFIED).
- autofold dry run (scratch/pb-fix/autofold.json): strict 46/10 on 56 -> 48/9 on 57; strictest 45/11 -> 47/10;
  output minus line 1 (scratch/pb-fix/FoldDryRun.lean) compiles, sixContactMin_of_open30 standard axioms (VERIFIED).
- Wording patch for pb-bypass's PanBerger.lean docstrings (not applied: rule "edit nothing else under ZInQKernel/"):
  scratch/pb-fix/PanBerger-wording.patch (Brinon–Conrad §6.1 -> §5 Thm 5.2.1; Fontaine Exp. VIII -> Exp. III 1.5).

## 2026-11-15 23:10 report
- Added isSemistableOverT_trivial_iff, isPstT_trivial (standard axioms, VERIFIED); `#` cardinal notation replaced by
  Cardinal.mk (contribution scan: 0 hits, VERIFIED). Reran axioms/#discharges/dry-run fold on the final file: all
  standard, r11r12 discharged, fold compiles (VERIFIED).
- Report docs/research/pb-fix.md written. Ratings: bergerPrintedT printed form; panPrintedT printed form under the
  eigenform reading.
