/-! # gt-rayclass: the two fields from the one leaf `ShimuraMainThmIDeligneY3AbU` -/

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT ShimuraGlue.Ray
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)

/-- **`RayClassCMAb` from the leaf `ShimuraMainThmIDeligneY3AbU` and `HomLinearLift`**, with no rigidity: the
witness `(Y, Φ)` of the leaf, with its abelian-scheme clause list `R1fpPropsAb`, is the witness of the field
(rayclass-cft's `rayClassCM_of` with `R1fpPropsAb` in place of `R1fpProps`; the glue `QHatIntegral`,
`CMBaseChange`, `CMAnalytic`, `RingOfIntegersGen` and `ClassNumberOneB` proved). -/
theorem rayClassCMAb_of (hL : ShimuraMainThmIDeligneY3AbU) (hHL : ZInQ.HomUnify.HomLinearLift) :
    ShimuraGlue.Ray.RayClassCMAb := by
  obtain ⟨Y, Φ, hAb, Ψ, hb, hU⟩ := hL
  have hCN : ClassNumberOneB := classNumberOneB_proof
  have hB : CMBaseChange := cmBaseChange
  have hA : CMAnalytic := cmAnalytic_of hHL
  refine ⟨Y, Φ, hAb, fun y P hP => ⟨fun h4 => ?_, fun h3 => ?_, fun h24 => ?_⟩⟩
  · refine embed_core hb hCN K4 finrank_K4 (qHatIntegral K4) y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, c4, -, -⟩ := obj_at hAb hU hB y P hP τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c4 h4
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K4 finrank_K4 (not_rat_of_disc y4_rel (by norm_num)) y4_rel ringOfIntegersGen_K4 τ _ hβO
      ?_ lam heig
    have := com_rel ρ hφ (P0 := 0) (Q0 := 1) (by rw [hφ2]; simp)
    simpa using this
  · refine embed_core hb hCN K3 finrank_K3 (qHatIntegral K3) y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, -, c3, -⟩ := obj_at hAb hU hB y P hP τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c3 h3
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K3 finrank_K3 (not_rat_of_disc y3_rel (by norm_num)) y3_rel ringOfIntegersGen_K3 τ _ hβO
      ?_ lam heig
    have := com_rel ρ hφ (P0 := -1) (Q0 := 1) (by rw [← hφ2]; simp; abel)
    simpa using this
  · refine embed_core hb hCN K24 finrank_K24 (qHatIntegral K24) y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, -, -, c24⟩ := obj_at hAb hU hB y P hP τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c24 h24
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K24 finrank_K24 (not_rat_of_disc y24_rel (by norm_num)) y24_rel ringOfIntegersGen_K24 τ _
      hβO ?_ lam heig
    have := com_rel ρ hφ (P0 := 0) (Q0 := 6) (by rw [hφ2]; simp)
    simpa using this

/-- **The field `rayClassCMAb` from the leaf `ShimuraMainThmIDeligneY3AbU` and the two textbook fields
`uniformizationLeafAll`, `gagaMorphism`** (which give `HomLatticeCorr`, hence `HomLinearLift`, through the
chain's `AvSplit.Final.h69`). -/
theorem rayClassCMAb_of_leaves (hL : ShimuraMainThmIDeligneY3AbU)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of hL (ZInQ.HomUnify.homLinearLift_of_corr (AvSplit.Final.h69 hUL hG))

/-- **The field `shimuraFamilyAb` from the same leaf** (rayclass-cft's `mainThmI_of_U`, then shimura-cft's
`shimuraFamilyAb_of_mainThmI`). -/
theorem shimuraFamilyAb_of_U (hL : ShimuraMainThmIDeligneY3AbU) : HDec.QMSplit.Moduli.ShimuraFamilyAb :=
  shimuraFamilyAb_of_mainThmI (mainThmI_of_U hL)

end RayClassCFT
