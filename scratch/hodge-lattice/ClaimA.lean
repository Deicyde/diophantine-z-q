import ZInQKernel.HDecomp.Faltings.Models

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- A regular function `i` on an open `U ∋ e(s')` whose pullback along the unit section vanishes
near `s'` gives an element `d i` of the local lattice `(ω_𝒢)_{s'}`. -/
theorem dCls_mem_omegaAt (U : 𝒢.G.left.Opens) (i : Γ(𝒢.G.left, U))
    (s' : Spec (CommRingCat.of (𝓞 L))) (hs' : 𝒢.unitSection s' ∈ U)
    (h0 : (Spec (CommRingCat.of (𝓞 L))).presheaf.germ (𝒢.unitSection ⁻¹ᵁ U) s' hs'
      (𝒢.unitSection.app U i) = 0)
    (hm : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit
      ((𝒢.specializes_genericUnit s').mem_open U.isOpen hs') i ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨_, hm⟩ ∈ 𝒢.omegaAt s' := by
  apply Submodule.subset_span
  refine ⟨𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs' i, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply]; exact h0
  · rw [TopCat.Presheaf.germ_stalkSpecializes_apply]; exact hm
  · congr 2
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

end ZInQ.DefFaltings.HodgeLattice
