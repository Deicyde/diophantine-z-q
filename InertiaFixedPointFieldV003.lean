import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Inertia-fixed geometric points have inertia-fixed finite coordinate fields

Let `X` be a locally finite-type scheme over a field `K`, `Ω` an algebraic closure of `K`, and
`w` a valuation subring of `Ω`. A geometric point `x : Spec Ω → X` fixed (under precomposition
with `Spec σ`) by every element of the inertia subgroup of `w` factors through an affine chart;
invariance of the point and injectivity of the chart force every coordinate of `x` to be fixed
by inertia. The coordinates of finitely many generators generate a finite intermediate field `M`,
contained in the fixed field of inertia, and `x` is the base change of a point `y : Spec M → X`.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace InertiaPointDescent

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- The inertia subgroup of `w`, as a subgroup of the automorphism group. -/
def inertiaGroup (w : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (w.inertiaSubgroup K).map (w.decompositionSubgroup K).subtype

theorem mem_inertiaGroup_iff (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ inertiaGroup (K := K) w ↔ PkgI2.IsInertia w σ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.2, hτ⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

/-- **Affine chart of a geometric point.** A point of a locally finite-type `K`-scheme is the
composite of `Spec` of a coordinate homomorphism `φ` with a monomorphism from the spectrum of a
finite-type `K`-algebra. -/
theorem exists_chart (X : Over (Spec (CommRingCat.of K))) [LocallyOfFiniteType X.hom]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ X) :
    ∃ (R : CommRingCat) (θ : CommRingCat.of K ⟶ R) (φ : R ⟶ CommRingCat.of Ω)
      (j : Spec R ⟶ X.left), Mono j ∧ RingHom.FiniteType θ.hom ∧
      θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω) ∧ Spec.map θ = j ≫ X.hom ∧
      Spec.map φ ≫ j = x.left := by
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
  refine ⟨Γ(X.left, U), θ, φ, e.inv ≫ U.ι, inferInstance, hθft, hcomp, ?_, ?_⟩
  · rw [hθ, Category.assoc]
  · rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']

/-- **Inertia-fixed points descend to inertia-fixed finite coordinate fields.** -/
theorem exists_inertia_fixed_field [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (X : Over (Spec (CommRingCat.of K))) [LocallyOfFiniteType X.hom]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ X)
    (hx : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ →
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.left = x.left) :
    ∃ M : IntermediateField K Ω, FiniteDimensional K M ∧
      M ≤ IntermediateField.fixedField (inertiaGroup (K := K) w) ∧
      ∃ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K M))) ⟶ X,
        Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left ∧
        ∃ (R : CommRingCat) (ψ : R ⟶ CommRingCat.of M) (j : Spec R ⟶ X.left),
          Mono j ∧ y.left = Spec.map ψ ≫ j := by
  classical
  obtain ⟨R, θ, φ, j, hj, hft, hcomp, hθ, hφx⟩ := exists_chart X x
  -- every coordinate is fixed by inertia
  have hfix : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ r : R, σ (φ r) = φ r := by
    intro σ hσ r
    have h1 := hx σ hσ
    rw [← hφx, ← Category.assoc, ← Spec.map_comp] at h1
    have h2 := (cancel_mono j).1 h1
    have h3 := Spec.map_injective h2
    exact congrArg (fun g => CommRingCat.Hom.hom g r) h3
  let _ : Algebra K R := θ.hom.toAlgebra
  have : Algebra.FiniteType K R := hft
  let f : R →ₐ[K] Ω :=
    { φ.hom with commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := K) (A := R)
  let t : Finset Ω := s.image f
  let M : IntermediateField K Ω := IntermediateField.adjoin K (t : Set Ω)
  have hfd : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := K) z).isIntegral
  have hgen : (s : Set R) ⊆ (M.toSubalgebra).comap f := by
    intro r hr
    apply IntermediateField.subset_adjoin K (t : Set Ω)
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  have hle : Algebra.adjoin K (s : Set R) ≤ (M.toSubalgebra).comap f := Algebra.adjoin_le hgen
  rw [hs] at hle
  have hM : ∀ r : R, f r ∈ M := fun r => hle (by trivial)
  have hMfix : M ≤ IntermediateField.fixedField (inertiaGroup (K := K) w) := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨r, -, rfl⟩ := Finset.mem_coe.mp hz |> Finset.mem_image.mp
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hfix σ ((mem_inertiaGroup_iff w σ).1 hσ) r
  let ψ : R →+* M := φ.hom.codRestrict M.toSubring (fun r => hM r)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom M.val.toRingHom = φ := by
    ext r
    rfl
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K M) := by
    ext a
    have h := congrArg (fun g => CommRingCat.Hom.hom g a) hcomp
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      ψ, RingHom.codRestrict_apply, IntermediateField.coe_algebraMap_apply] using h
  let y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K M))) ⟶ X :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ j) (by
      change (Spec.map (CommRingCat.ofHom ψ) ≫ j) ≫ X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap K M))
      rw [Category.assoc, ← hθ, ← Spec.map_comp, hθψ])
  refine ⟨M, hfd, hMfix, y, ?_, ⟨R, CommRingCat.ofHom ψ, j, hj, rfl⟩⟩
  change Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ j = x.left
  rw [← Category.assoc, ← Spec.map_comp, hψ, hφx]

/-- **The same statement for the kernel's abelian-variety points and Galois action.** -/
theorem exists_inertia_fixed_point_field [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (A : PkgI3.AbVar K) (x : A.Pt Ω)
    (hx : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x) :
    ∃ M : IntermediateField K Ω, FiniteDimensional K M ∧
      M ≤ IntermediateField.fixedField (inertiaGroup (K := K) w) ∧
      ∃ y : A.Pt M, Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left ∧
        ∃ (R : CommRingCat) (ψ : R ⟶ CommRingCat.of M) (j : Spec R ⟶ A.X.left),
          Mono j ∧ y.left = Spec.map ψ ≫ j := by
  refine exists_inertia_fixed_field w A.X x (fun σ hσ => ?_)
  have h := congrArg (fun z : A.Pt Ω => z.left) (hx σ hσ)
  exact h

end InertiaPointDescent
