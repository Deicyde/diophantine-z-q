# pb-fix2 results log

## 2026-11-16 01:00 start
- Base e479bc562 (wip/pb-fix). Build tree copied from ~/dzq-wt/nv-local (c137bf8c7; differs from base only in
  ZInQKernel/Contrib/OneProof/{PanBerger*,SGRDirect*}.lean): .lake/build and lean/.lake/build.
- Plan:
  * Berger: K_0 as printed = W(k_K)[1/p] = FractionRing (WittVector p k_K), k_K = residue field of
    O_K = {x ∈ K : ‖x‖ ≤ 1}; predicates on the underlying space V (tensor form (B ⊗ V)^{G_K}).
  * Pan: leaf stated for one GaloisRep with all hypotheses on it, printed (pst, HT distinct weights on V,
    geometric Frobenius in the conclusion); glue applies it to the contragredient ρ^∨ (GaloisRep), with
    de Rham/HT transfers by the trace-pairing isomorphism V' ≅ V^* (pure linear algebra).

## 2026-11-16 01:05-02:00 results (all VERIFIED: compiled)
- New file ZInQKernel/Contrib/OneProof/PanBergerPrinted.lean (imports PanBergerFix only; ~50 KB; contribution
  scan scripts/one_proof/sandbox/scan_contrib.py e479bc562 HEAD: 0 hits).
- Leaves: PanPrintedU (Pan 1.0.4 for one ρ; pst + HT-distinct printed on the underlying space V, tensor form;
  geometric Frobenius σ⁻¹ in the conclusion), BergerPrintedU (de Rham ⇒ pst on V, tensor form,
  K_0 = W(k_K)[1/p] = WittLoc p (resField p K)).
- Main: panBerger_of_printedU : PanPrintedU → BergerPrintedU → DSThm965 → DSThm966 → PanBerger, via the
  contragredient dualRep ρ (σ ↦ ρ(σ⁻¹)ᵀ): LocalIsDeRham ρ / DistinctHTWeights ρ (Hom forms on V) become the printed
  conditions on ρ^∨ by the trace-pairing isomorphism B ⊗ E^n ≅ Hom(E^n, B) (finrank_tensorInv_dualHom); no Sen/Tate
  input (AxSenTate, TateTwistInvariants not used).
- K_0 sanity: finrank_wittLoc ([W(k)[1/p]:Q_p] = [k:F_p], Teichmüller basis), resField_finite, card_resField
  (|k_K| = p^[K_0:Q_p]), finrank_K0W_le/pos/bot; isSemistableOverU_trivial_iff (trivial rep semistable over K ⇔
  dim B_st^{G_K} = [K_0:Q_p]), isPstU_trivial (given dim B_st^{G_Qp} = 1).
- Axioms: 18 declarations, all [propext, Classical.choice, Quot.sound] (scratch/pb-fix2/axioms-output.txt).
- #discharges: r11r12 by panBerger_of_printedU, still assumes PanPrintedU, BergerPrintedU, DSThm965, DSThm966;
  63 open hypotheses, 2107 theorems checked, 10 discharge one (scratch/pb-fix2/discharges-output.txt).
- autofold dry run: strict 46/10 on 56 -> 48/9 on 57; strictest 45/11 -> 47/10; output minus line 1
  (FoldDryRun.lean) compiles, sixContactMin_of_open30 standard axioms.
