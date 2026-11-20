import ZInQKernel.Contrib.CMSerreTateSupport.WildFiniteRestrictionV004
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Finite Galois fields of definition of actual geometric points

An actual point of a locally finite-type scheme factors through an affine
open. Finitely many coordinate-algebra generators have images in a
constructed finite Galois intermediate field. The resulting scalar
extension equality is proved on the native scheme morphism.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace SchemePointField

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- A finite-type algebra has image in a constructed finite Galois
intermediate field of a Galois extension, using its actual generators. -/
theorem finiteGalois_contains_image [IsGalois K Ω] {R : Type} [CommRing R]
    [Algebra K R] [Algebra.FiniteType K R] (f : R →ₐ[K] Ω) :
    ∃ L : FiniteGaloisIntermediateField K Ω, ∀ r : R, f r ∈ L.toIntermediateField := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := K) (A := R))
  let t : Finset Ω := s.image f
  let L := FiniteGaloisIntermediateField.adjoin K (t : Set Ω)
  have hgen : (s : Set R) ⊆ (L.toIntermediateField.toSubalgebra).comap f := by
    intro r hr
    apply FiniteGaloisIntermediateField.subset_adjoin K (t : Set Ω)
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  have hle : Algebra.adjoin K (s : Set R) ≤ (L.toIntermediateField.toSubalgebra).comap f :=
    Algebra.adjoin_le hgen
  rw [hs] at hle
  exact ⟨L, fun r => hle (by trivial)⟩

/-- Every actual geometric point in characteristic zero has a genuine
finite Galois field of definition. No point model is a hypothesis. -/
theorem exists_finiteGalois_point [CharZero K] [IsAlgClosure K Ω]
    (X : Over (Spec (CommRingCat.of K))) [LocallyOfFiniteType X.hom]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ X) :
    ∃ L : FiniteGaloisIntermediateField K Ω,
    ∃ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X,
      Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫ y.left = x.left := by
  classical
  let q0 : Spec (CommRingCat.of Ω) ⟶ X.left := x.left
  have hq0 : q0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := Over.w x
  let p : X.left := q0 (IsLocalRing.closedPoint Ω)
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q0 ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hs : s = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [hs]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q0 hrange
  have hq' : q' ≫ U.ι = q0 := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of Ω := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc,
      ← Category.assoc q', hq', hq0]
  have hθft : RingHom.FiniteType θ.hom := by
    have hft : LocallyOfFiniteType (Spec.map θ) := by rw [hθ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp hft
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  haveI : Algebra.FiniteType K Γ(X.left, U) := hθft
  let f : Γ(X.left, U) →ₐ[K] Ω :=
    { φ.hom with commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  obtain ⟨L, hL⟩ := finiteGalois_contains_image f
  let ψ : Γ(X.left, U) →+* L :=
    φ.hom.codRestrict L.toIntermediateField.toSubring (fun r => hL r)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom L.toIntermediateField.val.toRingHom = φ := by
    ext r
    rfl
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K L) := by
    ext a
    have h := congrArg (fun g => CommRingCat.Hom.hom g a) hcomp
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      ψ, RingHom.codRestrict_apply, IntermediateField.coe_algebraMap_apply] using h
  let y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) (by
      change (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ≫ X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L))
      rw [Category.assoc, Category.assoc, ← hθ, ← Spec.map_comp, hθψ])
  refine ⟨L, y, ?_⟩
  change Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι = q0
  rw [← Category.assoc, ← Spec.map_comp, hψ, hφ, Category.assoc,
    e.hom_inv_id_assoc, hq']

end SchemePointField
