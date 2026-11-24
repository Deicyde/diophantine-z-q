import ZInQKernel.Contrib.OneProof.Y3RepresentedFibres
import ZInQKernel.Contrib.OneProof.Y3SchemeQuotient
import ZInQKernel.Contrib.OneProof.Y3HodgePrint
import ZInQKernel.Contrib.OneProof.FiniteGeometricSurjectivity

/-! Uniformization of the actual rational quotient on complex points. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Filter
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open HDec HDec.QMSplit.Moduli
open HDec.HSyn.G0Split.FibreQM HDec.HSyn.G0Split.FibreQM.PeriodGlue
open HDec.HSyn.G0Split.FibreQM.PeriodMapH
open RayClassCFT ShimuraCFT
open SGRSplit Y3Fix Y3RouteA HDec.VertWitness HDec.ModelGlue
open scoped CategoryTheory.Obj Topology

namespace Y3P1j

set_option backward.isDefEq.respectTransparency false

private theorem holFamily_comp {X Z : Scheme.{0}} (f : X ⟶ Z)
    {φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)} (h : ShimuraSplit.IsHolFamily φ) :
    ShimuraSplit.IsHolFamily (fun τ => φ τ ≫ f) := by
  constructor
  · intro U
    exact h.1 (f ⁻¹ᵁ U)
  · intro U s τ hτ
    obtain ⟨g, hg, he⟩ := h.2 (f ⁻¹ᵁ U) (f.app U s) τ hτ
    refine ⟨g, hg, he.mono fun z hz hpos => ?_⟩
    have hreg : ShimuraSplit.regVal U s (φ ⟨z, hpos⟩ ≫ f) =
        ShimuraSplit.regVal (f ⁻¹ᵁ U) (f.app U s) (φ ⟨z, hpos⟩) := by
      by_cases hmem : ShimuraSplit.ptC (φ ⟨z, hpos⟩ ≫ f) ∈ U
      · have hmem' : ShimuraSplit.ptC (φ ⟨z, hpos⟩) ∈ f ⁻¹ᵁ U := hmem
        rw [ShimuraSplit.regVal, dite_eq_left hmem, ShimuraSplit.regVal, dite_eq_left hmem']
        exact LeafQM.AV.Pin.ImagePlane.ev_comp _ _ hmem _
      · have hmem' : ShimuraSplit.ptC (φ ⟨z, hpos⟩) ∉ f ⁻¹ᵁ U := hmem
        rw [ShimuraSplit.regVal, dite_eq_right hmem, ShimuraSplit.regVal, dite_eq_right hmem']
    exact hreg.trans (hz hpos)

/-- On the actual complex points, the rational quotient is uniformized by
the upper half-plane with fibres the orbits of the positive normalizer. -/
theorem exists_complex_quotient_period_map
    {Y Z : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (π : Y ⟶ Z)
    [IsFinite π.left] [Surjective π.left]
    (hquot : ∀ (y y' : fieldPt ℂ ⟶ Y) (P Q : QML3 ℂ),
      Φ ℂ y = M3.mk P → Φ ℂ y' = M3.mk Q →
        (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    (hΦ : Y3Fix.R1fpPropsAbP Y Φ)
    (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint) (hL : QMTwistLattice) :
    ∃ F : UpperHalfPlane → (fieldPt ℂ ⟶ Z),
      Function.Surjective F ∧ ShimuraSplit.IsHolFamily (fun τ => (F τ).left) ∧
      ∀ τ τ', F τ = F τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ' := by
  obtain ⟨Ψ, hB, hU⟩ := Y3Hodge.deligneH_of_print hD Y Φ hΦ
  have hb := Y3Fix.body_of_H hB
  have hu := Y3Fix.units_of_H hU
  have hu₁ : (1 : BAQˣ) ∈ OhatU := ⟨OhatQ_one, by simpa using OhatQ_one⟩
  let F : UpperHalfPlane → (fieldPt ℂ ⟶ Z) := fun τ => Ψ τ 1 ≫ π
  refine ⟨F, ?_, holFamily_comp π.left (hb.2.2.1 1), ?_⟩
  · intro z
    obtain ⟨y, hy⟩ := exists_lift_of_finite_surjective_of_isAlgClosed π.left z.left
    let y' : fieldPt ℂ ⟶ Y := Over.homMk y (calc
      y ≫ Y.hom = y ≫ (π.left ≫ Z.hom) := congrArg (y ≫ ·) π.w.symm
      _ = (y ≫ π.left) ≫ Z.hom := (Category.assoc _ _ _).symm
      _ = z.left ≫ Z.hom :=
        congrArg (fun a : Spec (CommRingCat.of ℂ) ⟶ Z.left => a ≫ Z.hom) hy
      _ = (fieldPt ℂ).hom := z.w)
    have hy' : y' ≫ π = z := Over.OverMorphism.ext hy
    obtain ⟨τ₀, g, hτg⟩ := hb.1 y'
    obtain ⟨γ, hγ, u, hu', hg⟩ := exists_pos_decomp classNumberOneB_proof g
    let τ := (iotaGL (binv γ) (nrd_binv_pos hγ).ne') • τ₀
    have hτu : Ψ τ u = y' :=
      ((hb.2.1 τ₀ g τ u).mpr (dcRel_of_decomp hγ τ₀ hg)).symm.trans hτg
    obtain ⟨P, hP, hPτ⟩ := hu 1 hu₁ τ
    obtain ⟨Q, hQ, hQτ⟩ := hu u hu' τ
    have hr := (hL P Q τ τ hPτ hQτ).mpr
      ⟨1, one_mem_gammaStar, one_smul _ _⟩
    exact ⟨τ, ((hquot (Ψ τ 1) (Ψ τ u) P Q hP hQ).mpr hr).trans
      (congrArg (fun a => a ≫ π) hτu |>.trans hy')⟩
  · intro τ τ'
    obtain ⟨P, hP, hPτ⟩ := hu 1 hu₁ τ
    obtain ⟨Q, hQ, hQτ⟩ := hu 1 hu₁ τ'
    exact (hquot (Ψ τ 1) (Ψ τ' 1) P Q hP hQ).trans (hL P Q τ τ' hPτ hQτ)

/-- The quotient of the actual rational fine model has the complex analytic
period map supplied by its canonical-model data. -/
theorem exists_uniformized_proper_quotient_of_z30
    (hI : Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hL : QMTwistLattice) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (𝒜 : QMAbSchemeP Y.left)
      (Z : Over (Spec (CommRingCat.of ℚ))) (π : Y ⟶ Z)
      (F : UpperHalfPlane → (fieldPt ℂ ⟶ Z)),
      IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Represents Y 𝒜 ∧
      IsProper Z.hom ∧ IsFinite π.left ∧ Surjective π.left ∧
      (∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
        IsFibreOf 𝒜.toQMFamily y.left P → IsFibreOf 𝒜.toQMFamily y'.left Q →
          (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q))) ∧
      Function.Surjective F ∧ ShimuraSplit.IsHolFamily (fun τ => (F τ).left) ∧
      ∀ τ τ', F τ = F τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ' := by
  obtain ⟨Y, 𝒜, hp, hs, hU⟩ := y3RepresentableQ_of_z30 hI
  have hT := AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  obtain ⟨Φ, hΦ, hΦfib⟩ := Y3Audit.exists_fineModuliAt_of_rep hT hp hs hU
  obtain ⟨Z, π, hfin, hproper, hsurj, hfib⟩ :=
    exists_twistMark_quotient_geometric_fibres hp hs hU
  have : Surjective π.left := ⟨hsurj⟩
  obtain ⟨F, hsur, hhol, horb⟩ := exists_complex_quotient_period_map π
    (fun y y' P Q hP hQ => hfib ℂ y y' P Q ((hΦfib ℂ y P).mp hP) ((hΦfib ℂ y' Q).mp hQ))
    hΦ hD hL
  exact ⟨Y, 𝒜, Z, π, F, hp, hs, hU, hproper, hfin, ‹_›, hfib Qbar,
    hsur, hhol, horb⟩

end Y3P1j

#print axioms Y3P1j.exists_complex_quotient_period_map
#print axioms Y3P1j.exists_uniformized_proper_quotient_of_z30
