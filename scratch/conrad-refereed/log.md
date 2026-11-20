# Conrad row results

- Base: `ae799aef495474d2dfaf16cd8581375011623230`.
- Exact row: `HDec.G0Galois.C8Conrad.ConradAppB = ConradAppBQp ∧ ConradPropB3Qp`.
- Existing CFT: unit filtration at zero maps onto abelianized inertia;
  `cyc_of_isArtinLift`: `χ(Art(u)) = u⁻¹`; `pow_card_eq_one_of_mem_inertia`:
  the residual character takes inertia values of order dividing `φ(p^k)`.
- Existing periods: `CloudB3W11.axSenTate_proof` and
  `CloudB3W11.tateTwistInvariants_proof` over finite `K`.
  No proved arbitrary-character period criterion on inertia at the base.
- Input: `SerreAppB.LocalArtin.SerreA6Prop6` (Serre Ch. III Appendix A6;
  locator UNVERIFIED): (ii) twisted admissibility for all coefficient embeddings
  iff (iv) the cancellation identity on an open subgroup of integer units at `artinMap K`.
- Output: `conradAppB_of_refereed : SerreA6Prop6 → C8Conrad.ConradAppB`.
- Forward: `HasHTWeights {w}` → pure splitting at `−w` → periods →
  Serre (iv) → near-one formula at `ℚ_p`.
- Reverse: near-one formula at `ℚ_p` → Serre (iv) → identity period →
  `conradHTMult p (charRep ψ) n = [E:ℚ_p]`; no prior Hodge–Tate assumption.
- Normalization: arithmetic Artin; `wt_Conrad(χ) = +1`; `wt_manuscript(χ) = −1`.
- Tex 765–767: geometric modular normalization gives cyclotomic power one at
  weight two; power zero requires arithmetic modular normalization.
- First guarded Lake build: interrupted during a redundant pre-existing dependency
  rebuild. Verification uses matching pinned base artifacts in unchanged dependencies.

- Final build: `lake --old --no-cache build +ZInQKernel.Contrib.OneProof.ConradRefereed.DischargesFocused`;
  all 9 new modules built with a serialized compiler.
- Axiom audit: 42 theorems; standard axioms only.

```text
DISCHARGES [conradAppB] by HDec.G0Galois.C8Conrad.conradAppB_of_refereed
  still assumes: [HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.SerreA6Prop6]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 1 open hypotheses, 6572 theorems checked, 1 discharge one
```

`#print axioms`:

```text
'HDec.G0Galois.C8Conrad.Bridges.conradAbelianChar_artinLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.artinNearOneOnAbelianization_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges.0.HDec.G0Galois.C8Conrad.Bridges.cp_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges.0.HDec.G0Galois.C8Conrad.Bridges.ht_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.pureHT_of_hasHTWeights' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.range_restrictGalois' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.exists_artinLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.artinNearOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges.0.HDec.G0Galois.C8Conrad.Bridges.charRep_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges.0.HDec.G0Galois.C8Conrad.Bridges.extend_conradLA' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges.0.HDec.G0Galois.C8Conrad.Bridges.identityLine_mem_Ysp' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges.0.HDec.G0Galois.C8Conrad.Bridges.finiteDimensional_Ysp_charRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ZInQKernel.Contrib.OneProof.ConradRefereed.Bridges.0.HDec.G0Galois.C8Conrad.Bridges.finrank_Ysp_charRep_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.conradHTMult_of_identityLine' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.conradAppBQp_of_nearOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.Bridges.conradPropB3Qp_of_identityWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.identityLine_of_serreTwistAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.conradIdentityWeight_of_serre' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.topology_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.range_eq_fixing' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.character_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.forall_fixing_iff_forall_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.normOne_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.character_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.openSubgroup_normOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.normOneUnits_eq_unitFiltration' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.serreUnits_eq_normOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin.serreA6NormEquivalence_of_prop6' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.serreTwistAdmissible_of_pureHT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.norm_sum_le_of_forall_le'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.eq_one_of_pow_eq_one_of_norm_sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.conradNearOne_of_serre' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.conradAppB_of_refereed' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.norm_eq_one_of_norm_sub_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.norm_mul_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.norm_prod_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.norm_algEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.mem_unitBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.isOpen_unitBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.G0Galois.C8Conrad.SerreAppB.norm_normUnits_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
