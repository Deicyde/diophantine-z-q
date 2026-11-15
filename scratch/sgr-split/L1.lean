import ZInQKernel.OneProof.H.TailZ16
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk

noncomputable section

namespace SGRL1

open CategoryTheory AlgebraicGeometry Limits

def SmoothGeomConnIntegral : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), Smooth f →
    GeometricallyConnected f → GeometricallyIntegral f

/-- Stalks of a smooth scheme over a field are domains. -/
theorem isDomain_stalk_of_smooth {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
  have hsm := f.smooth_appLE hU hV hVU
  let _ : Field Γ(Spec (CommRingCat.of k), ⊤) :=
    (ZInQ.Contrib.Dim.isField_sections_spec k ⊤ Set.univ_nonempty).toField
  let _ : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := (f.appLE ⊤ V hVU).hom.toAlgebra
  have : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := hsm
  let x' : V := ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk x'
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  exact (ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) (hV.primeIdealOf x').asIdeal (X.presheaf.stalk x)).1

/-- **`SmoothGeomConnIntegral` holds.** -/
theorem smoothGeomConnIntegral : SmoothGeomConnIntegral := by
  intro K _ X f hs hc
  refine ⟨fun L _ y Z fst snd h => ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback h hs
  have : ConnectedSpace Z := hc.geometrically_connectedSpace y fst snd h
  have : IsReduced Z := LeafQM.AV.R1UnivRigid.isReduced_of_smooth snd
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  have : IrreducibleSpace Z :=
    TauCeti.AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk Z
      (fun x => isDomain_stalk_of_smooth snd x)
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

end SGRL1

#print axioms SGRL1.smoothGeomConnIntegral
