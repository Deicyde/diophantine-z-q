import ZInQKernel.Contrib.G9.BdREmb
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.DVRFiltration
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.Graded
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.TateSenCp

/-! # The filtration of `B_dR` by a uniformizer, and the graded pieces of `D_dR`

With a uniformizer `ϖ` of `B_dR^+` whose image `u ∈ B_dR` satisfies `σ(u) = χ(σ) u`, the filtration
`u^i B_dR^+` of `B_dR` and the maps `u^i y ↦ θ(y)` satisfy the hypotheses of the abstract graded
theorem, with `C = ℂ_p` and `σ` acting on `ℂ_p(i)` by `χ(σ)^i σ`.
-/

set_option autoImplicit false

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

theorem hkappa (c : ℚ_[p]) :
    algebraMap ℚ_[p] (BdR p) c = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (qpToPlus p c) :=
  qpToBdR_eq p c

theorem isFractionRingPlus : IsFractionRing (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) :=
  BdrKer.Cp.isFractionRing_BDeRham p

attribute [local instance] isFractionRingPlus

theorem isDVRPlus : IsDiscreteValuationRing (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  BdrKer.Cp.isDiscreteValuationRing_BDeRhamPlus p

attribute [local instance] isDVRPlus

/-- `θ` is `ℚ_p`-linear. -/
theorem thetaPlusCp_algebraMap (c : ℚ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p c) = algebraMap ℚ_[p] ℂ_[p] c :=
  thetaPlusCp_qpToPlus p c

/-- The filtration `u^i B_dR^+` of `B_dR`, `u` the image of a uniformizer. -/
abbrev filBdRU (u : (BdR p)ˣ) (i : ℤ) : Submodule ℚ_[p] (BdR p) :=
  filU (qpToPlus p) (hkappa p) u i

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]

/-- **Graded pieces of `D_dR` against the twisted invariants**, for a uniformizer `ϖ` of `B_dR^+`
with `σ(ϖ) = χ(σ) ϖ` in `B_dR`. -/
theorem finrank_grD_bdR {ϖ : BDeRhamPlus 𝓞_ℂ_[p] p} (hϖ : Irreducible ϖ) (u : (BdR p)ˣ)
    (hu : (u : BdR p) = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) ϖ)
    (hσu : ∀ σ : GQp p, bdrAct p σ (u : BdR p) = algebraMap ℚ_[p] (BdR p) (cycPow p σ 1) * u)
    (a : GQp p → BdR p →ₗ[ℚ_[p]] BdR p) (ha : ∀ σ x, a σ x = bdrAct p σ x)
    (c : ℤ → GQp p → ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p])
    (hc : ∀ i σ z, c i σ z = cycPow p σ i • cpAct p σ z)
    (r : GQp p → V →ₗ[ℚ_[p]] V)
    (hHfin : ∀ i, FiniteDimensional ℚ_[p] (invT (c i) r))
    (hHsum : ∀ J : Finset ℤ, ∑ i ∈ J, finrank ℚ_[p] (invT (c i) r) ≤ finrank ℚ_[p] V)
    (hdR : finrank ℚ_[p] (invT a r) = finrank ℚ_[p] V) (i : ℤ) :
    finrank ℚ_[p] (grD (filBdRU p u) a r i) = finrank ℚ_[p] (invT (c i) r) := by
  have hker : RingHom.ker (BdrKer.Cp.thetaPlusCp p) = Ideal.span {ϖ} := by
    rw [BdrKer.Cp.ker_thetaPlusCp, ← BdrKer.Cp.maximalIdeal_BDeRhamPlus,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  have hτu : ∀ σ : GQp p, ∀ j : ℤ,
      a σ ↑(u ^ j) = algebraMap ℚ_[p] (BdR p) (cycPow p σ j) * ↑(u ^ j) := fun σ j => by
    rw [ha]
    exact zpow_equivariant (bdrAct p σ) (fun j => cycPow p σ j) (cycPow_zero' p σ)
      (fun x y => cycPow_add' p σ x y) (hσu σ) j
  have hmul : ∀ σ : GQp p, ∀ x y, a σ (x * y) = a σ x * a σ y := fun σ x y => by
    rw [ha, ha, ha, map_mul]
  have hR : ∀ σ : GQp p, ∀ y, a σ (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) y) =
      algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (DR.bdrPlusMap p (oAct p σ) y) := fun σ y => by
    rw [ha, bdrAct, DR.bdrMap, IsLocalization.map_eq]
  have hFst : ∀ j σ (x : BdR p), x ∈ filBdRU p u j → a σ x ∈ filBdRU p u j :=
    fun j σ x hx => mem_filU_map (qpToPlus p) (hkappa p) (a σ) (hmul σ) _ (hR σ) _ (hτu σ) j x hx
  refine finrank_grD_eq (filBdRU p u)
    (fun j => gU (qpToPlus p) (hkappa p) (BdrKer.Cp.thetaPlusCp p) (thetaPlusCp_algebraMap p) j)
    a c r
    (filU_anti (qpToPlus p) (hkappa p) hu) (filU_exhaustive (qpToPlus p) (hkappa p) hu hϖ)
    (filU_separated (qpToPlus p) (hkappa p) hu hϖ)
    (fun j x => gU_eq_zero_iff (qpToPlus p) (hkappa p) (BdrKer.Cp.thetaPlusCp p) hu
      (thetaPlusCp_algebraMap p) hker j x)
    hFst (fun j σ x hx => ?_) hHfin hHsum hdR i
  rw [gU_map (qpToPlus p) (hkappa p) (BdrKer.Cp.thetaPlusCp p) (thetaPlusCp_algebraMap p) (a σ)
    (hmul σ) _ (hR σ)
    (cpAct p σ) (fun y => thetaPlusCp_bdrPlusMap p σ y) _ (hτu σ) j x hx, hc]

end

end DeRhamHTMult
