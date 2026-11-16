/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PDivisibleGroup_add_eq_height_of_hasDimension_of_cartierDuality
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CartierDuality
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Dimension
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_BaseChange
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_PDivisibleGroup_cotangentBaseChange_bijective
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_PDivisibleGroup_IsCartierDual_baseChange
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_PDivisibleGroup_CartierDuality_finrank_cotangent_one_add_finrank_cotangent_one_eq_height

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PDivisibleGroup_add_eq_height_of_hasDimension_of_cartierDuality
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

open scoped TensorProduct

namespace PDivProp3

variable {R : Type} [CommRing R] [IsLocalRing R]

-- [port T8] local notation "k" expanded in place

theorem finrank_tensor_quotient {J : Ideal R} (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    Module.finrank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] (R ⧸ J)) = 1 := by
  have hmap : J.map (algebraMap R (IsLocalRing.ResidueField R)) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact hJ hx
  have e : ((IsLocalRing.ResidueField R) ⧸ J.map (algebraMap R (IsLocalRing.ResidueField R))) ≃ₗ[(IsLocalRing.ResidueField R)] (IsLocalRing.ResidueField R) ⊗[R] (R ⧸ J) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (IsLocalRing.ResidueField R) J).toLinearEquiv
  rw [← e.finrank_eq]
  have e' : ((IsLocalRing.ResidueField R) ⧸ J.map (algebraMap R (IsLocalRing.ResidueField R))) ≃ₗ[(IsLocalRing.ResidueField R)] (IsLocalRing.ResidueField R) :=
    Submodule.quotEquivOfEqBot _ (by rw [hmap])
  rw [e'.finrank_eq, Module.finrank_self]

theorem finrank_tensor_pi_quotient {J : Ideal R} (hJ : J ≤ IsLocalRing.maximalIdeal R) (n : ℕ) :
    Module.finrank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] (Fin n → R ⧸ J)) = n := by
  rw [(TensorProduct.piRight R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) (fun _ : Fin n => R ⧸ J)).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_tensor_quotient hJ, smul_eq_mul]
  exact mul_one n

variable {p h : ℕ}

theorem finrank_cotangent_baseChange_one (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (G : PDivisibleGroup R p h) {n : ℕ} (hn : G.HasDimension n) :
    Module.finrank (IsLocalRing.ResidueField R) ((G.baseChange (IsLocalRing.ResidueField R)).Cotangent 1) = n := by

  have e1 : ((IsLocalRing.ResidueField R) ⊗[R] G.Cotangent 1) ≃ₗ[(IsLocalRing.ResidueField R)]
      (PDivisibleGroup.Hopf.augIdeal (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] G.level 1)).Cotangent :=
    LinearEquiv.ofBijective (G.cotangentBaseChange (IsLocalRing.ResidueField R) 1) (G.cotangentBaseChange_bijective (IsLocalRing.ResidueField R) 1)
  have e2 : ((IsLocalRing.ResidueField R) ⊗[R] G.Cotangent 1) ≃ₗ[(IsLocalRing.ResidueField R)] ((IsLocalRing.ResidueField R) ⊗[R] (Fin n → R ⧸ Ideal.span {(p : R) ^ 1})) :=
    (hn 1).some.baseChange R (IsLocalRing.ResidueField R) _ _
  change Module.finrank (IsLocalRing.ResidueField R) (PDivisibleGroup.Hopf.augIdeal (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] G.level 1)).Cotangent = n
  rw [← e1.finrank_eq, e2.finrank_eq]
  refine finrank_tensor_pi_quotient ?_ n
  rw [pow_one, Ideal.span_le, Set.singleton_subset_iff]
  exact hp

end PDivProp3

open PDivProp3 in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {p h : ℕ} [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') {n n' : ℕ}
    (hn : G.HasDimension n) (hn' : G'.HasDimension n') : n + n' = h := by

  haveI : CharP (IsLocalRing.ResidueField R) p := by
    rw [CharP.charP_iff_prime_eq_zero Fact.out]
    rw [← map_natCast (algebraMap R (IsLocalRing.ResidueField R)) p,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact hp

  obtain ⟨Dk⟩ := PDivisibleGroup.IsCartierDual.baseChange (⟨D⟩ : G.IsCartierDual G')
    (IsLocalRing.ResidueField R)
  have hsum := Dk.finrank_cotangent_one_add_finrank_cotangent_one_eq_height
  rwa [finrank_cotangent_baseChange_one hp G hn, finrank_cotangent_baseChange_one hp G' hn'] at hsum
