/-
Tate's Hodge-Tate decomposition for p-divisible groups over the ring of integers of a finite extension of `ℚ_p`
(J. Tate, *p-divisible groups*, Proc. Conf. Local Fields, Driebergen 1966, Springer 1967, §4, Cor. 2 of Thm 3).

The theorem is proved in Anthropic FLT (anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0) as
`PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers`;
its import cone is vendored under `Vendor/AnthropicFLT/` (see `PORTING.md`). The statement below is upstream's,
verbatim, with the same local instance and simp-lemma settings.

This is supporting material. It is about p-divisible groups over `O_K`, not abelian varieties, and does not
prove `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`.
-/
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers

set_option autoImplicit false

attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule
attribute [-simp] PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent PDivisibleGroup.baseChange_level HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one
attribute [-simp] PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map

open scoped TensorProduct

namespace ZInQ.Contrib.CloudB3SC3PDivHodge

/-- **Tate's Hodge-Tate decomposition for p-divisible groups** (Tate 1967, §4, Cor. 2 of Thm 3). For `K` a
finite extension of `ℚ_p` inside `ℚ̄_p` and `G` a p-divisible group of height `h` and dimension `n` over the
ring of integers of `K`: `n ≤ h`, and `ℂ_p ⊗_{ℚ_p} V_p(G)` has a `ℂ_p`-basis `b` such that every
`σ ∈ Gal(ℚ̄_p/ℚ_p)` fixing `K` (acting on `ℂ_p ⊗ V_p(G)` diagonally) sends `b i` to `χ(σ) • b i` for `i < n` and
fixes `b i` for `n ≤ i`, where `χ` is the `p`-adic cyclotomic character. -/
theorem pDivisibleGroup_hodgeTate
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ}
    (hn : G.HasDimension n) :
    n ≤ h ∧
    ∃ b : Module.Basis (Fin h) ℂ_[p]
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)))),
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ x : PadicAlgCl p, τ x = σ x) → ∀ i : Fin h,
        TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap
            ((G.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p]) (b i) =
          (algebraMap ℚ_[p] ℂ_[p]
              (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^
            (if (i : ℕ) < n then 1 else 0) • b i :=
  PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
    p K G hn

end ZInQ.Contrib.CloudB3SC3PDivHodge
