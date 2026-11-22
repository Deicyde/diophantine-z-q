import ZInQKernel.Contrib.OneProof.Y3QuotientSphere
import ZInQKernel.Contrib.OneProof.H.TailZ21

/-! The complex-point topology defined by regular functions on the rational
scheme. Period maps are continuous for this topology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open LeafQM.AV
open scoped Topology

namespace Y3P1j

variable (X : Over (Spec (CommRingCat.of ℚ)))

/-- The classical topology on the complex points of a rational scheme,
using evaluation of regular functions on each open. -/
@[instance_reducible]
def complexPointTopology : TopologicalSpace (fieldPt ℂ ⟶ X) :=
  generateFrom {S | ∃ (U : X.left.Opens) (s : Γ(X.left, U)) (V : Set ℂ), IsOpen V ∧
    S = {y | ShimuraSplit.ptC y.left ∈ U ∧ ShimuraSplit.regVal U s y.left ∈ V}}

attribute [local instance] complexPointTopology

private theorem isOpen_regVal (U : X.left.Opens) (s : Γ(X.left, U)) (V : Set ℂ) (hV : IsOpen V) :
    IsOpen {y : fieldPt ℂ ⟶ X | ShimuraSplit.ptC y.left ∈ U ∧ ShimuraSplit.regVal U s y.left ∈ V} :=
  isOpen_generateFrom_of_mem ⟨U, s, V, hV, rfl⟩

/-- Holomorphy as tested by regular functions implies continuity on complex
points equipped with their classical topology. -/
theorem continuous_of_isHolFamily {F : UpperHalfPlane → (fieldPt ℂ ⟶ X)}
    (hF : ShimuraSplit.IsHolFamily (fun t => (F t).left)) : Continuous F := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨U, s, V, hV, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have htU : ShimuraSplit.ptC (F t).left ∈ U := ht.1
  have htV : ShimuraSplit.regVal U s (F t).left ∈ V := ht.2
  obtain ⟨g, hg, heq⟩ := hF.2 U s t htU
  have he : ∀ᶠ t' in 𝓝 t, ShimuraSplit.regVal U s (F t').left = g t' :=
    ShimuraSplit.eventually_of_complex heq
  have htV' : g t ∈ V := (mem_of_mem_nhds he) ▸ htV
  have hpre : ∀ᶠ t' : UpperHalfPlane in 𝓝 t, g t' ∈ V :=
    (hg.continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt).eventually (hV.mem_nhds htV')
  filter_upwards [(hF.1 U).mem_nhds htU, he, hpre] with t' ht' he' ht'V
  exact ⟨ht', he'.symm ▸ ht'V⟩

/-- Complex points can be separated if each pair is contained in one affine
open of the rational scheme. -/
theorem t2Space_complexPointTopology
    (hAff : ∀ x y : X.left, ∃ U : X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U) :
    T2Space (fieldPt ℂ ⟶ X) := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨U, hU, hx, hy⟩ := hAff (ShimuraSplit.ptC x.left) (ShimuraSplit.ptC y.left)
  have hval : ∃ s : Γ(X.left, U), ShimuraSplit.regVal U s x.left ≠ ShimuraSplit.regVal U s y.left := by
    by_contra! he
    apply hxy
    apply Over.OverMorphism.ext
    apply X6Glue.ev_injective U hU x.left y.left hx hy
    apply RingHom.ext
    intro s
    have h := he s
    simp only [ShimuraSplit.regVal, dite_eq_left hx, dite_eq_left hy] at h
    exact h
  obtain ⟨s, hs⟩ := hval
  obtain ⟨V, W, hV, hW, hxV, hyW, hd⟩ := t2_separation hs
  refine ⟨_, _, isOpen_regVal X U s V hV, isOpen_regVal X U s W hW,
    ⟨hx, hxV⟩, ⟨hy, hyW⟩, Set.disjoint_left.mpr fun z hz hz' => ?_⟩
  exact Set.disjoint_left.mp hd hz.2 hz'.2

/-- A proper smooth curve has Hausdorff complex points in the
regular-function topology on its rational scheme. -/
theorem t2Space_complexPoints_of_proper_smooth [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] : T2Space (fieldPt ℂ ⟶ X) := by
  classical
  apply t2Space_complexPointTopology
  intro x y
  obtain ⟨U, hU⟩ := exists_affineOpens_forall_mem_of_smooth_curve X.hom {x, y}
  exact ⟨U.1, U.2, hU x (by simp), hU y (by simp)⟩

open HDec in
/-- The actual complex points of a proper smooth quotient with the asserted
period data are homeomorphic to the Riemann sphere. -/
theorem complexPoints_homeomorphic_sphere [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] {F : UpperHalfPlane → (fieldPt ℂ ⟶ X)}
    (hF : Function.Surjective F) (hhol : ShimuraSplit.IsHolFamily (fun t => (F t).left))
    (hOrb : ∀ t t', F t = F t' ↔ ∃ g ∈ PkgI1.GammaStar, g • t = t')
    (hj : PkgI1.QMHauptmodul) : Nonempty ((fieldPt ℂ ⟶ X) ≃ₜ OnePoint ℂ) := by
  let R := Setoid.ker F
  obtain ⟨e⟩ := period_quotient_homeomorphic_sphere F hOrb hj
  have : CompactSpace (Quotient R) := e.symm.surjective.compactSpace e.symm.continuous
  have : T2Space (fieldPt ℂ ⟶ X) := t2Space_complexPoints_of_proper_smooth X
  let f : Quotient R → (fieldPt ℂ ⟶ X) := Quotient.lift F (fun _ _ h => h)
  have hf : Continuous f := (continuous_of_isHolFamily X hhol).quotient_lift _
  have hb : Function.Bijective f := by
    constructor
    · rintro ⟨t⟩ ⟨t'⟩ h
      exact Quotient.sound h
    · intro x
      obtain ⟨t, rfl⟩ := hF x
      exact ⟨Quotient.mk R t, rfl⟩
  let q : Quotient R ≃ₜ (fieldPt ℂ ⟶ X) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hb) hf
  exact ⟨q.symm.trans e⟩

end Y3P1j

#print axioms Y3P1j.complexPoints_homeomorphic_sphere
