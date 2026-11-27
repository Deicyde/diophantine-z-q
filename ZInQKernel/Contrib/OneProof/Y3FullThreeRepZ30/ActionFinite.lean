import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits

/-!
# Finiteness of the projection leg of a finite group action relation

For a finite type `G` and a scheme `X`, the map `∐ (_ : G), X ⟶ X` that is the
identity on each copy is finite. The proof writes it as a base change of the
codiagonal `∐ (_ : G), Spec R ⟶ Spec R` along any map `X ⟶ Spec R`, by finitary
extensivity. The codiagonal is `Spec` of the diagonal ring map `R ⟶ (G → R)`,
which is finite.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Y3QuotientDescent

open AlgebraicGeometry

variable {X : Scheme.{u}} {G : Type u}

/-- The codiagonal over an affine scheme is `Spec` of the diagonal ring map. -/
theorem codiag_eq (R : CommRingCat.{u}) :
    (Sigma.desc fun _ : G => 𝟙 (Spec R)) =
      sigmaSpec (fun _ : G => R) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (G → R)) : R ⟶ CommRingCat.of (G → R)) := by
  apply Sigma.hom_ext
  intro g
  rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem isFinite_codiag [Finite G] (R : CommRingCat.{u}) :
    IsFinite (Sigma.desc fun _ : G => 𝟙 (Spec R)) := by
  rw [codiag_eq]
  have : IsFinite (Spec.map
      (CommRingCat.ofHom (algebraMap R (G → R)) : R ⟶ CommRingCat.of (G → R))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

/-- The codiagonal pulled back along `h : X ⟶ Spec R`, by finitary extensivity. -/
theorem isPullback_codiag [Finite G] (R : CommRingCat.{u}) (h : X ⟶ Spec R) :
    IsPullback
      (Sigma.desc fun p : G × PUnit.{u+1} =>
        pullback.fst (𝟙 (Spec R)) h ≫ Sigma.ι (fun _ : G => Spec R) p.1)
      (Sigma.desc fun p : G × PUnit.{u+1} =>
        pullback.snd (𝟙 (Spec R)) h ≫ Sigma.ι (fun _ : PUnit.{u+1} => X) p.2)
      (Sigma.desc fun _ : G => 𝟙 (Spec R)) (Sigma.desc fun _ : PUnit.{u+1} => h) :=
  FinitaryPreExtensive.isPullback_sigmaDesc (fun _ : G => 𝟙 (Spec R))
    (fun _ : PUnit.{u+1} => h)

/-- The unique-index coproduct folded back to `X`. -/
noncomputable def unitDesc (X : Scheme.{u}) : (∐ fun _ : PUnit.{u+1} => X) ⟶ X :=
  Sigma.desc fun _ => 𝟙 X

instance (X : Scheme.{u}) : IsIso (unitDesc X) := by
  refine ⟨Sigma.ι (fun _ : PUnit.{u+1} => X) PUnit.unit, ?_, ?_⟩
  · apply Sigma.hom_ext
    rintro ⟨⟩
    simp [unitDesc]
  · simp [unitDesc]

@[reassoc]
theorem snd_lift_eq_id (R : CommRingCat.{u}) (h : X ⟶ Spec R) :
    pullback.snd (𝟙 (Spec R)) h ≫ pullback.lift h (𝟙 X) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← pullback.condition,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

/-- From `∐ (_ : G), X` to the pulled-back coproduct. -/
noncomputable def relToPb (R : CommRingCat.{u}) (h : X ⟶ Spec R) :
    (∐ fun _ : G => X) ⟶ ∐ fun _ : G × PUnit.{u+1} => pullback (𝟙 (Spec R)) h :=
  Sigma.desc fun g => pullback.lift h (𝟙 X) (by simp) ≫
    Sigma.ι (fun _ : G × PUnit.{u+1} => pullback (𝟙 (Spec R)) h) (g, PUnit.unit)

/-- Its inverse. -/
noncomputable def pbToRel (R : CommRingCat.{u}) (h : X ⟶ Spec R) :
    (∐ fun _ : G × PUnit.{u+1} => pullback (𝟙 (Spec R)) h) ⟶ ∐ fun _ : G => X :=
  Sigma.desc fun p => pullback.snd (𝟙 (Spec R)) h ≫ Sigma.ι (fun _ : G => X) p.1

instance (R : CommRingCat.{u}) (h : X ⟶ Spec R) : IsIso (relToPb (G := G) R h) := by
  refine ⟨pbToRel R h, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro g
    simp [relToPb, pbToRel]
  · apply Sigma.hom_ext
    rintro ⟨g, ⟨⟩⟩
    simp only [pbToRel, relToPb, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc,
      Category.comp_id]
    rw [← Category.assoc, snd_lift_eq_id, Category.id_comp]

theorem codiagT_eq_comp (R : CommRingCat.{u}) (h : X ⟶ Spec R) :
    (Sigma.desc fun _ : G => 𝟙 X) = relToPb R h ≫
      (Sigma.desc fun p : G × PUnit.{u+1} =>
        pullback.snd (𝟙 (Spec R)) h ≫ Sigma.ι (fun _ : PUnit.{u+1} => X) p.2) ≫
      unitDesc X := by
  apply Sigma.hom_ext
  intro g
  simp [relToPb, unitDesc]

/-- The fold map `∐ (_ : G), X ⟶ X` is finite for finite `G`. -/
theorem isFinite_codiagT [Finite G] (X : Scheme.{u}) :
    IsFinite (Sigma.desc fun _ : G => 𝟙 X) := by
  have hc := isFinite_codiag (G := G) Γ(X, ⊤)
  have hs : IsFinite (Sigma.desc fun p : G × PUnit.{u+1} =>
      pullback.snd (𝟙 (Spec Γ(X, ⊤))) X.toSpecΓ ≫
        Sigma.ι (fun _ : PUnit.{u+1} => X) p.2) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_codiag _ X.toSpecΓ) hc
  rw [codiagT_eq_comp _ X.toSpecΓ]
  infer_instance

end Y3QuotientDescent
