import ZInQKernel.Contrib.AdelicNormalizer.Congruence

/-!
# Exact source and consumer checks for G1

These closed applications pin the actual objects in the manuscript count.
They do not replace independent mathematical review or Astra acceptance.
-/

namespace G1.Checks

theorem exact_normalizer_count : Nat.card (N ⧸ D0) = 4 := card_normalizer_quotient

theorem exact_level_count : Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0) = 36 :=
  card_level_quotient

theorem exact_manuscript_factorization :
    Nat.card (N ⧸ D3) = Nat.card (N ⧸ D0) *
      Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0) := card_GammaPrime_eq_indices

theorem exact_manuscript_count : Nat.card (N ⧸ D3) = 144 := card_GammaPrime

theorem exact_principal_congruence (u : K0) :
    u.val ∈ K3 ↔ ∃ z ∈ completedOrder, (u.val : BA) - 1 = 3 * z :=
  mem_K3_iff_congruence u

theorem exact_rational_order_residue_count :
    Nat.card (GlueRepo.A1.O ⧸ RingHom.ker IntegralComparison.rationalReduction)ˣ = 72 :=
  IntegralComparison.card_units_rationalQuotient

end G1.Checks

#check G1.scalarEquiv
#check G1.ScalarExtension.scalarExtensionEquiv'
#check G1.IntegralComparison.mem_completedOrder_iff_tensor
#check G1.IntegralComparison.rationalQuotientEquiv
#check G1.quaternionEquiv
#check G1.mem_N
#check G1.mem_globalDenom
#check G1.normalizerQuotientEquiv
#check G1.local_quotient_card
#check G1.Z0_eq_integralScalars
#check G1.reduction3
#check G1.mem_K3_iff_congruence
#check G1.range_reduction3_integralScalar
#check G1.levelQuotientEquiv
#check G1.Checks.exact_normalizer_count
#check G1.Checks.exact_level_count
#check G1.Checks.exact_manuscript_factorization
#check G1.Checks.exact_manuscript_count
#check G1.Checks.exact_rational_order_residue_count

#print axioms G1.scalarEquiv
#print axioms G1.ScalarExtension.scalarExtensionEquiv'
#print axioms G1.IntegralComparison.mem_completedOrder_iff_tensor
#print axioms G1.IntegralComparison.rationalQuotientEquiv
#print axioms G1.IntegralComparison.rationalReduction_eq_localReduction
#print axioms G1.quaternionEquiv
#print axioms G1.mem_N
#print axioms G1.mem_globalDenom
#print axioms G1.normalizerQuotientEquiv
#print axioms G1.local_quotient_card
#print axioms G1.Z0_eq_integralScalars
#print axioms G1.reduction3_surjective
#print axioms G1.range_reduction3_integralScalar
#print axioms G1.K3_in_N_normal
#print axioms G1.mem_K3_iff_congruence
#print axioms G1.levelQuotientEquiv
#print axioms G1.card_GammaPrime_eq_indices
#print axioms G1.card_GammaPrime
#print axioms G1.Checks.exact_manuscript_count
#print axioms G1.Checks.exact_rational_order_residue_count
