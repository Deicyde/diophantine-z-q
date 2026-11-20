import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Coverings of the topological Riemann sphere have continuous sections.
This uses the two stereographic charts and uniqueness of lifting on the
connected overlap. -/

noncomputable section

open Set Function Metric

namespace IsCoveringMap

/-- Two open simply connected charts with a connected nonempty overlap
give a continuous section of every surjective covering. -/
theorem exists_section_of_two_charts
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X}
    (hp : IsCoveringMap p) (hsur : Surjective p) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    [SimplyConnectedSpace U] [SimplyConnectedSpace V]
    [LocallyPathConnectedSpace U] [LocallyPathConnectedSpace V]
    (hInter : IsConnected (U ∩ V)) :
    ∃ F : C(X, E), p ∘ F = id := by
  classical
  obtain ⟨x, hxU, hxV⟩ := hInter.nonempty
  obtain ⟨e, he⟩ := hsur x
  let iU : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iV : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨FU, ⟨hUe, hFU⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts iU ⟨x, hxU⟩ e he
  obtain ⟨FV, ⟨hVe, hFV⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts iV ⟨x, hxV⟩ e he
  let rU : (↥(U ∩ V)) → U := fun y => ⟨y, y.property.1⟩
  let rV : (↥(U ∩ V)) → V := fun y => ⟨y, y.property.2⟩
  have : PreconnectedSpace (U ∩ V : Set X) := Subtype.preconnectedSpace hInter.isPreconnected
  have hr : FU ∘ rU = FV ∘ rV := hp.eq_of_comp_eq
    (FU.continuous.comp (continuous_subtype_val.subtype_mk _))
    (FV.continuous.comp (continuous_subtype_val.subtype_mk _))
    (by
      rw [← Function.comp_assoc, ← Function.comp_assoc, hFU, hFV]
      rfl)
    ⟨x, hxU, hxV⟩ (hUe.trans hVe.symm)
  have hIn : ∀ y ∉ U, y ∈ V := fun y hy =>
    (show y ∈ U ∪ V from hUV.symm ▸ mem_univ y).resolve_left hy
  let F : X → E := fun y => if hy : y ∈ U then FU ⟨y, hy⟩ else FV ⟨y, hIn y hy⟩
  have hF_U (y : U) : F y = FU y := dite_eq_left y.property
  have hF_V (y : V) : F y = FV y := by
    by_cases hy : y.val ∈ U
    · exact (dite_eq_left hy).trans (congrFun hr ⟨y.val, hy, y.property⟩)
    · exact dite_eq_right hy
  have hF : Continuous F := by
    have hcu : ContinuousOn F U := continuousOn_iff_continuous_domRestrict.mpr
      (FU.continuous.congr fun y => (hF_U y).symm)
    have hcv : ContinuousOn F V := continuousOn_iff_continuous_domRestrict.mpr
      (FV.continuous.congr fun y => (hF_V y).symm)
    rw [← continuousOn_univ, ← hUV]
    exact ContinuousOn.union_of_isOpen hcu hcv hU hV
  refine ⟨⟨F, hF⟩, funext fun y => ?_⟩
  by_cases hy : y ∈ U
  · exact (congrArg p (hF_U ⟨y, hy⟩)).trans (congrFun hFU ⟨y, hy⟩)
  · exact (congrArg p (hF_V ⟨y, hIn y hy⟩)).trans (congrFun hFV ⟨y, hIn y hy⟩)

private abbrev SphereTwo := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private def sphereTwoChart (a : SphereTwo) :
    ({a}ᶜ : Set SphereTwo) ≃ₜ EuclideanSpace ℝ (Fin 2) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e := stereographic' 2 a
  exact (Homeomorph.setCongr (stereographic'_source a).symm).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target a)).trans (Homeomorph.Set.univ _)))

private theorem connected_sphereTwo_overlap {a b : SphereTwo} (hab : a ≠ b) :
    IsConnected (({a}ᶜ ∩ {b}ᶜ) : Set SphereTwo) := by
  let U : Set SphereTwo := {a}ᶜ
  let b' : U := ⟨b, by change b ≠ a; exact Ne.symm hab⟩
  let e := sphereTwoChart a
  have hb : IsConnected ({e b'}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp [← Module.finrank_eq_rank]) _
  have hc : IsConnected ({b'}ᶜ : Set U) := by
    convert hb.image e.symm e.symm.continuous.continuousOn using 1
    ext y
    simp [Homeomorph.image_symm, e.injective.eq_iff]
  convert hc.image (Subtype.val : U → SphereTwo) continuous_subtype_val.continuousOn using 1
  ext y
  constructor
  · rintro ⟨hy, hyb⟩
    exact ⟨⟨y, hy⟩, fun h => hyb (congrArg Subtype.val h), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.property, fun h => hz (Subtype.ext h)⟩

/-- Every surjective covering of the unit two-sphere admits a section. -/
theorem exists_section_sphereTwo {E : Type*} [TopologicalSpace E]
    {p : E → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hp : IsCoveringMap p) (hsur : Surjective p) :
    ∃ F : C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, E), p ∘ F = id := by
  let a₀ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  let a : SphereTwo := ⟨a₀, by simp [a₀]⟩
  let b : SphereTwo := ⟨-a₀, by simp [a₀]⟩
  have hab : a ≠ b := by
    intro h
    have h' := congrArg (fun y : SphereTwo => y.val 0) h
    norm_num [a, b, a₀] at h'
  let U : Set SphereTwo := {a}ᶜ
  let V : Set SphereTwo := {b}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hV : IsOpen V := isClosed_singleton.isOpen_compl
  have hCov : U ∪ V = univ := eq_univ_of_forall fun x => by
    by_cases hx : x = a
    · exact Or.inr (by change x ≠ b; exact hx ▸ hab)
    · exact Or.inl hx
  have : SimplyConnectedSpace U := (sphereTwoChart a).toHomotopyEquiv.simplyConnectedSpace
  have : SimplyConnectedSpace V := (sphereTwoChart b).toHomotopyEquiv.simplyConnectedSpace
  have : LocallyPathConnectedSpace U := (sphereTwoChart a).symm.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace V := (sphereTwoChart b).symm.locallyPathConnectedSpace
  exact hp.exists_section_of_two_charts hsur hU hV hCov (connected_sphereTwo_overlap hab)

/-- Every surjective covering of a space homeomorphic to the Riemann sphere
admits a continuous section. -/
theorem exists_section_of_homeomorphic_onePointComplex
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X}
    (hp : IsCoveringMap p) (hsur : Surjective p) (e : X ≃ₜ OnePoint ℂ) :
    ∃ F : C(X, E), p ∘ F = id := by
  let q : X ≃ₜ SphereTwo := e.trans
    (onePointEquivSphereOfFinrankEq (ι := Fin 3) (by simp [Complex.finrank_real_complex]))
  obtain ⟨g, hg⟩ := (hp.homeomorph_comp q).exists_section_sphereTwo (q.surjective.comp hsur)
  refine ⟨g.comp ⟨q, q.continuous⟩, funext fun x => q.injective ?_⟩
  exact congrFun hg (q x)

end IsCoveringMap

#print axioms IsCoveringMap.exists_section_of_homeomorphic_onePointComplex
