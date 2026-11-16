import ZInQKernel.Contrib.OneProof.PicDictionary

/-! # pic-dict: `FiniteOfFiniteKerPts` (a homomorphism with finitely many `K̄`-points in its kernel is finite) -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- Over a closed point `b`, there are finitely many `K̄`-points (they are the `K`-embeddings of the finite
extension `κ(b)` into `K̄`). -/
theorem finite_pts_over {B : AbVar K} (b : B.X.left) (hb : IsClosed {b}) :
    {y : B.Pt (AlgebraicClosure K) |
      y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b}.Finite := by
  haveI : IsFinite (B.X.left.fromSpecResidueField b ≫ B.X.hom) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hb
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ := Spec.preimage (B.X.left.fromSpecResidueField b ≫ B.X.hom)
  have hφ : Spec.map φ = B.X.left.fromSpecResidueField b ≫ B.X.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K (B.X.left.residueField b) := φ.hom.toAlgebra
  haveI : Module.Finite K (B.X.left.residueField b) := hfin
  let mk : (B.X.left.residueField b →ₐ[K] AlgebraicClosure K) → (Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      B.X.left) := fun ψ =>
    Spec.map (CommRingCat.ofHom (ψ : B.X.left.residueField b →+* AlgebraicClosure K)) ≫
      B.X.left.fromSpecResidueField b
  have key : ∀ y : B.Pt (AlgebraicClosure K),
      y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b → ∃ ψ, y.left = mk ψ := by
    intro y hy
    have e1 : ∀ (x : B.X.left) (hx : x = b) (ψ : B.X.left.residueField x ⟶
        CommRingCat.of (AlgebraicClosure K)), ∃ ψ' : B.X.left.residueField b ⟶
          CommRingCat.of (AlgebraicClosure K),
        Spec.map ψ ≫ B.X.left.fromSpecResidueField x = Spec.map ψ' ≫ B.X.left.fromSpecResidueField b := by
      intro x hx ψ; subst hx; exact ⟨ψ, rfl⟩
    have hy' : (Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left y.left).1 = b := hy
    obtain ⟨ψ', hψ'⟩ := e1 _ hy' (Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left y.left).2
    have hyl : y.left = Spec.map ψ' ≫ B.X.left.fromSpecResidueField b := by
      rw [← hψ']
      exact ((Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left).symm_apply_apply y.left).symm
    have hw : φ ≫ ψ' = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, ← Category.assoc, ← hyl]
      exact Over.w y
    refine ⟨{ toRingHom := ψ'.hom, commutes' := fun a => ?_ }, hyl⟩
    exact congrArg (fun χ => χ.hom a) hw
  apply Set.Finite.of_finite_image (f := fun y : B.Pt (AlgebraicClosure K) => y.left)
  · refine (Set.finite_range mk).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨ψ, h⟩ := key y hy
    exact ⟨ψ, h.symm⟩
  · intro y _ y' _ h
    exact Over.OverMorphism.ext h

/-- A fibre of a homomorphism on `K̄`-points is empty or a translate of the kernel. -/
theorem finite_fiber_pts {A B : AbVar K} (f : Hom A B)
    (hS : {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite) (y : B.Pt (AlgebraicClosure K)) :
    {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = y}.Finite := by
  by_cases h : ∃ x₀, x₀ ≫ f.hom = y
  · obtain ⟨x₀, hx₀⟩ := h
    refine (hS.image (· * x₀)).subset ?_
    intro x hx
    refine ⟨x * x₀⁻¹, ?_, by simp⟩
    change (x * x₀⁻¹) ≫ f.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hx, hx₀, mul_inv_cancel]
  · convert Set.finite_empty
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨x, hx⟩

/-- Over a closed point there are finitely many closed points. -/
theorem finite_closed_over {A B : AbVar K} (f : Hom A B)
    (hS : {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite) (b : B.X.left) (hb : IsClosed {b}) :
    {a : A.X.left | IsClosed {a} ∧ f.hom.left a = b}.Finite := by
  have hU : {x : A.Pt (AlgebraicClosure K) |
      (x ≫ f.hom).left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b}.Finite := by
    refine ((finite_pts_over b hb).biUnion fun y _ => finite_fiber_pts f hS y).subset ?_
    intro x hx
    exact Set.mem_biUnion (x := x ≫ f.hom) hx rfl
  refine (hU.image fun x => x.left (IsLocalRing.closedPoint (AlgebraicClosure K))).subset ?_
  rintro a ⟨ha, hab⟩
  obtain ⟨x, hx⟩ := exists_pt_of_isClosed (B := A) a ha
  refine ⟨x, ?_, hx⟩
  change f.hom.left (x.left _) = b
  rw [hx, hab]

/-- `f` is quasi-finite at every closed point. -/
theorem quasiFiniteAt_of_isClosed {A B : AbVar K} (f : Hom A B)
    (hS : {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite) (a : A.X.left) (ha : IsClosed {a}) :
    f.hom.left.QuasiFiniteAt a := by
  haveI : IsProper (f.hom.left ≫ B.X.hom) := by rw [Over.w f.hom]; infer_instance
  haveI : IsProper f.hom.left := IsProper.of_comp f.hom.left B.X.hom
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hb : IsClosed {f.hom.left a} := by
    rw [← Set.image_singleton]; exact f.hom.left.isClosedMap _ ha
  have hpre : IsClosed (f.hom.left ⁻¹' {f.hom.left a}) := hb.preimage f.hom.left.continuous
  have hcp : (closedPoints (f.hom.left.fiber (f.hom.left a))).Finite := by
    refine Set.Finite.of_finite_image (f := f.hom.left.fiberι (f.hom.left a)) ?_
      (f.hom.left.fiberι _).isEmbedding.injective.injOn
    refine (finite_closed_over f hS _ hb).subset ?_
    rintro _ ⟨p, hp, rfl⟩
    have e : f.hom.left.fiberι (f.hom.left a) p =
        ((f.hom.left.fiberHomeo (f.hom.left a)) p : A.X.left) := by
      rw [Scheme.Hom.fiberHomeo_apply]
    refine ⟨?_, ?_⟩
    · rw [e]
      have h1 := (f.hom.left.fiberHomeo (f.hom.left a)).isClosedMap _ hp
      rw [Set.image_singleton] at h1
      have h2 := hpre.isClosedMap_subtype_val _ h1
      rwa [Set.image_singleton] at h2
    · rw [e]
      exact ((f.hom.left.fiberHomeo (f.hom.left a)) p).2
  haveI := JacobsonSpace.discreteTopology hcp
  exact isOpen_discrete _

/-- **`FiniteOfFiniteKerPts` is a theorem.** -/
theorem finiteOfFiniteKerPts : FiniteOfFiniteKerPts := by
  intro K _ A B f hS
  haveI : IsProper (f.hom.left ≫ B.X.hom) := by rw [Over.w f.hom]; infer_instance
  haveI : IsProper f.hom.left := IsProper.of_comp f.hom.left B.X.hom
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  haveI : LocallyQuasiFinite f.hom.left := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    by_contra hne
    have hc : (f.hom.left.quasiFiniteLocus : Set A.X.left)ᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      exact hne (SetLike.coe_injective (h.trans TopologicalSpace.Opens.coe_top.symm))
    obtain ⟨a, ha, hca⟩ := nonempty_inter_closedPoints hc
      (f.hom.left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed)
    exact ha (quasiFiniteAt_of_isClosed f hS a hca)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.hom.left

end PicDict
