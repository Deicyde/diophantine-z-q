import Mathlib

/-! # kf-glue: the two point lemmas (prototype; copied into New.lean) -/

noncomputable section

namespace KfGluePoints

open CategoryTheory AlgebraicGeometry Limits

abbrev Qb : Type := AlgebraicClosure ℚ

/-- The ring of a finite affine scheme over `Spec ℚ̄`, and its structure map from `ℚ̄`. -/
def phi (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) :
    CommRingCat.of Qb ⟶ Γ(P, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of Qb)).inv ≫ q.appTop

theorem q_eq (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb)) :
    q = P.isoSpec.hom ≫ Spec.map (phi P q) := by
  have h := Scheme.isoSpec_hom_naturality q
  rw [Scheme.isoSpec_Spec_hom] at h
  rw [phi, Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

theorem phi_finite (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q] :
    (phi P q).hom.Finite := by
  rw [phi, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (Scheme.Hom.finite_appTop q)
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)

/-- Sections of `q` correspond to ring maps `ψ : Γ(P) → ℚ̄` with `ψ ∘ φ = id`. -/
theorem section_iff (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb))
    (ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb) :
    (Spec.map ψ ≫ P.isoSpec.inv) ≫ q = 𝟙 _ ↔ phi P q ≫ ψ = 𝟙 _ := by
  have hq := q_eq P q
  have e : (Spec.map ψ ≫ P.isoSpec.inv) ≫ q = Spec.map (phi P q ≫ ψ) := by
    conv_lhs => rw [hq]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  rw [e, ← Spec.map_id]
  exact Spec.map_injective.eq_iff

/-- **A nonempty finite scheme over `Spec ℚ̄` has a section.** -/
theorem exists_section (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q]
    [Nonempty P] : ∃ s : Spec (CommRingCat.of Qb) ⟶ P, s ≫ q = 𝟙 _ := by
  have : IsAffine P := isAffine_of_isAffineHom q
  have hB : Nontrivial Γ(P, ⊤) := by
    rw [← PrimeSpectrum.nonempty_iff_nontrivial]
    exact ⟨P.isoSpec.hom (Classical.arbitrary P)⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(P, ⊤)
  let f : Qb →+* (Γ(P, ⊤) ⧸ m) := (Ideal.Quotient.mk m).comp (phi P q).hom
  have hf : f.IsIntegral :=
    (RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
      (phi_finite P q)).to_isIntegral
  have : m.IsMaximal := hm
  have hbij := IsAlgClosed.ringHom_bijective_of_isIntegral f hf
  let e := RingEquiv.ofBijective f hbij
  let ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb :=
    CommRingCat.ofHom ((e.symm : (Γ(P, ⊤) ⧸ m) →+* Qb).comp (Ideal.Quotient.mk m))
  refine ⟨Spec.map ψ ≫ P.isoSpec.inv, (section_iff P q ψ).mpr ?_⟩
  ext r
  change e.symm (f r) = r
  exact e.symm_apply_apply r

/-- **A finite scheme over `Spec ℚ̄` has finitely many sections.** -/
theorem finite_sections (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q] :
    {s : Spec (CommRingCat.of Qb) ⟶ P | s ≫ q = 𝟙 _}.Finite := by
  have : IsAffine P := isAffine_of_isAffineHom q
  letI : Algebra Qb Γ(P, ⊤) := (phi P q).hom.toAlgebra
  have : Module.Finite Qb Γ(P, ⊤) := phi_finite P q
  have hpre : ∀ s : Spec (CommRingCat.of Qb) ⟶ P, ∃ ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb,
      Spec.map ψ = s ≫ P.isoSpec.hom := fun s => Spec.map_surjective _
  choose ψ hψ using hpre
  have hs : ∀ s, s = Spec.map (ψ s) ≫ P.isoSpec.inv := fun s => by
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let g : {s : Spec (CommRingCat.of Qb) ⟶ P | s ≫ q = 𝟙 _} → (Γ(P, ⊤) →ₐ[Qb] Qb) := fun s =>
    { toRingHom := (ψ s.1).hom
      commutes' := fun r => by
        have h1 : phi P q ≫ ψ s.1 = 𝟙 _ := by
          rw [← section_iff P q, ← hs]; exact s.2
        exact congrArg (fun k : CommRingCat.of Qb ⟶ CommRingCat.of Qb => k.hom r) h1 }
  have hg : Function.Injective g := by
    intro s t hst
    apply Subtype.ext
    rw [hs s.1, hs t.1]
    have : ψ s.1 = ψ t.1 := by
      ext x; exact congrArg (fun k : Γ(P, ⊤) →ₐ[Qb] Qb => k x) hst
    rw [this]
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

/-- **`LiftQbarPoints`'s content.** -/
theorem liftQbar (X Y : Scheme.{0}) (F : X ⟶ Y) (hF : IsFinite F) (hs : Surjective F)
    (y : Spec (CommRingCat.of Qb) ⟶ Y) : ∃ x : Spec (CommRingCat.of Qb) ⟶ X, x ≫ F = y := by
  have : IsFinite F := hF
  have : Surjective F := hs
  have : Nonempty (Limits.pullback F y : Scheme.{0}) := by
    obtain ⟨p, -⟩ := (pullback.snd F y).surjective (Classical.arbitrary _)
    exact ⟨p⟩
  obtain ⟨s, hs'⟩ := exists_section (pullback F y) (pullback.snd F y)
  refine ⟨s ≫ pullback.fst F y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs', Category.id_comp]

/-- **`FiniteFibreQbarPoints`'s content.** -/
theorem finiteFibreQbar (X Y : Scheme.{0}) (F : X ⟶ Y) (hF : IsFinite F)
    (y : Spec (CommRingCat.of Qb) ⟶ Y) :
    {x : Spec (CommRingCat.of Qb) ⟶ X | x ≫ F = y}.Finite := by
  have : IsFinite F := hF
  have := (finite_sections (pullback F y) (pullback.snd F y)).to_subtype
  let ℓ : {x : Spec (CommRingCat.of Qb) ⟶ X | x ≫ F = y} →
      {s : Spec (CommRingCat.of Qb) ⟶ pullback F y | s ≫ pullback.snd F y = 𝟙 _} := fun x =>
    ⟨pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]), pullback.lift_snd _ _ _⟩
  have hℓ : Function.Injective ℓ := by
    intro x x' h
    apply Subtype.ext
    have h1 : pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]) =
        pullback.lift x'.1 (𝟙 _) (by rw [x'.2, Category.id_comp]) := congrArg Subtype.val h
    have h2 := congrArg (fun t : Spec (CommRingCat.of Qb) ⟶ pullback F y => t ≫ pullback.fst F y) h1
    simpa using h2
  exact Set.finite_coe_iff.mp (Finite.of_injective ℓ hℓ)

end KfGluePoints
