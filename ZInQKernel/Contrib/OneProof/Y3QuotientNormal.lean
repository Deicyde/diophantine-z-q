import ZInQKernel.Contrib.OneProof.Y3SchemeQuotient
import ZInQKernel.Contrib.OneProof.InvariantRingNormal
import ZInQKernel.Contrib.OneProof.H.TailR

/-! Normality and dimension of the actual finite level-three quotient. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane LeafQM.AV.R1UnivRigid
open Y3Fix Y3RouteA

namespace Y3P1j

variable {Y : Over (Spec (CommRingCat.of ℚ))} {𝒜 : QMAbSchemeP Y.left}

set_option backward.isDefEq.respectTransparency false

/-- Normality and dimension descend to the finite level-and-twist quotient
of a smooth irreducible represented curve. -/
theorem exists_normal_twistMark_scheme_quotient
    (hP : IsProper Y.hom) (hS : SmoothOfRelativeDimension 1 Y.hom)
    (hU : Represents Y 𝒜) (hI : IrreducibleSpace Y.left) :
    ∃ (Z : Over (Spec (CommRingCat.of ℚ))) (π : Y ⟶ Z)
      (hπ : ∀ g, (twistMarkSchemeAction hU (Y3Audit.isLocallyNoetherian_of_smooth_Q Y hS)
        g).asIso.hom ≫ π.left = π.left),
      IsFinite π.left ∧ IsProper Z.hom ∧ Function.Surjective π.left.base ∧
      IsIntegral Z.left ∧ ZInQ.Contrib.CurvesG.IsNormalScheme Z.left ∧
      topologicalKrullDim Z.left = 1 ∧
      (∀ V : Z.left.Opens, Set.range (π.left.app V) =
        {s | ∀ g, (twistMarkSchemeAction hU (Y3Audit.isLocallyNoetherian_of_smooth_Q Y hS)
          g).asIso.hom.appLE (π.left ⁻¹ᵁ V) (π.left ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) := by
  have hN := Y3Audit.isLocallyNoetherian_of_smooth_Q Y hS
  let ρ := twistMarkSchemeAction hU hN
  obtain ⟨Z, π, hπ, hfin, hZP, hsurj, -, hinj, hsections, -⟩ :=
    exists_twistMark_scheme_quotient hP hS hU hN
  have hunormal (V : Z.left.Opens) (hV : IsAffineOpen V) (hne : (V : Set Z.left).Nonempty) :
      IsDomain Γ(Z.left, V) ∧ IsIntegrallyClosed Γ(Z.left, V) := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨y, rfl⟩ := hsurj z
    let U := π.left ⁻¹ᵁ V
    have hUa : IsAffineOpen U := hV.preimage π.left
    obtain ⟨hD, hNormal⟩ := HDec.HeckeRestCurve.chartNormal Y U hS hI hUa ⟨y, hz⟩
    let φ := (π.left.app V).hom
    have hdom : IsDomain Γ(Z.left, V) := (hinj V).isDomain φ
    let _ : Algebra Γ(Z.left, V) Γ(Y.left, U) := φ.toAlgebra
    let act (g : twistMarkGroup hU hN) : Γ(Y.left, U) →+* Γ(Y.left, U) :=
      ((ρ g).asIso.hom.appLE U U (by rw [← Scheme.Hom.comp_preimage, hπ g])).hom
    exact ⟨hdom, isIntegrallyClosed_of_range_eq_fixed (hinj V) act (hsections V)⟩
  have hstalk (z : Z.left) : IsDomain (Z.left.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.left.presheaf.stalk z) := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ := Z.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ z) isOpen_univ
    obtain ⟨hD, hN⟩ := hunormal V hV ⟨z, hzV⟩
    let z' : V := ⟨z, hzV⟩
    let _ := TopCat.Presheaf.algebra_section_stalk Z.left.presheaf z'
    have := hV.isLocalization_stalk z'
    let p := (hV.primeIdealOf z').asIdeal
    have := Ideal.primeCompl_le_nonZeroDivisors p
    exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ this,
      isIntegrallyClosed_of_isLocalization _ p.primeCompl this⟩
  have : IrreducibleSpace Z.left := hsurj.irreducibleSpace π.left.continuous
  have : ∀ z : Z.left, _root_.IsReduced (Z.left.presheaf.stalk z) := fun z => by
    have := (hstalk z).1
    infer_instance
  have : IsReduced Z.left := isReduced_of_isReduced_stalk Z.left
  have : topologicalKrullDim Z.left = 1 := by
    have : Surjective π.left := ⟨hsurj⟩
    rw [← ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_finite_surjective π.left,
      ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension Y.hom 1]
    norm_num
  exact ⟨Z, π, hπ, hfin, hZP, hsurj, isIntegral_of_irreducibleSpace_of_isReduced Z.left,
    fun z => (hstalk z).2, this, hsections⟩

end Y3P1j

#print axioms Y3P1j.exists_normal_twistMark_scheme_quotient
