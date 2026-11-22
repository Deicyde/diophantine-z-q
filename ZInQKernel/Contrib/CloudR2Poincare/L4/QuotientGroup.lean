import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientDescent

/-!
# The group structure descended to the actual stabilizer quotient

All operations and group axioms descend through the supplied finite-flat
kernel-pair quotient. Its existence remains a labelled input; the group-object
structure and homomorphism property are proved, not record fields assumed here.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

section Transport

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A Q : C} [GrpObj A] (q : A ⟶ Q)
    [Epi q] [Epi (𝟙 (𝟙_ C) ⊗ₘ q)] [Epi (q ⊗ₘ 𝟙 (𝟙_ C))]
    [Epi ((q ⊗ₘ q) ⊗ₘ q)]
    (m : Q ⊗ Q ⟶ Q) (hm : (q ⊗ₘ q) ≫ m = μ[A] ≫ q)
    (v : Q ⟶ Q) (hv : q ≫ v = ι[A] ≫ q)

/-- Epimorphic transport of the actual group-object operations and axioms. -/
@[reducible] def grpObjOfEpi (hv : q ≫ v = ι[A] ≫ q) : GrpObj Q where
  one := η[A] ≫ q
  mul := m
  inv := v
  one_mul := by
    apply (cancel_epi (𝟙 (𝟙_ C) ⊗ₘ q)).1
    calc
      (𝟙 (𝟙_ C) ⊗ₘ q) ≫ ((η[A] ≫ q) ▷ Q) ≫ m =
          (η[A] ▷ A) ≫ (q ⊗ₘ q) ≫ m := by
            simp only [tensorHom_comp_whiskerRight_assoc, Category.id_comp,
              whiskerRight_comp_tensorHom_assoc]
      _ = (η[A] ▷ A) ≫ μ[A] ≫ q := by rw [hm]
      _ = (𝟙 (𝟙_ C) ⊗ₘ q) ≫ (λ_ Q).hom := by
        rw [MonObj.one_mul_assoc, id_tensorHom, leftUnitor_naturality]
  mul_one := by
    apply (cancel_epi (q ⊗ₘ 𝟙 (𝟙_ C))).1
    calc
      (q ⊗ₘ 𝟙 (𝟙_ C)) ≫ (Q ◁ (η[A] ≫ q)) ≫ m =
          (A ◁ η[A]) ≫ (q ⊗ₘ q) ≫ m := by
            simp only [tensorHom_comp_whiskerLeft_assoc, Category.id_comp,
              whiskerLeft_comp_tensorHom_assoc]
      _ = (A ◁ η[A]) ≫ μ[A] ≫ q := by rw [hm]
      _ = (q ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Q).hom := by
        rw [MonObj.mul_one_assoc, tensorHom_id, rightUnitor_naturality]
  mul_assoc := by
    apply (cancel_epi ((q ⊗ₘ q) ⊗ₘ q)).1
    calc
      ((q ⊗ₘ q) ⊗ₘ q) ≫ (m ▷ Q) ≫ m = ((μ[A] ≫ q) ⊗ₘ q) ≫ m := by
        rw [tensorHom_comp_whiskerRight_assoc, hm]
      _ = (μ[A] ▷ A) ≫ μ[A] ≫ q := by
        rw [← whiskerRight_comp_tensorHom_assoc, hm]
      _ = (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ μ[A] ≫ q := by rw [MonObj.mul_assoc_assoc]
      _ = (α_ A A A).hom ≫ (q ⊗ₘ (q ⊗ₘ q)) ≫ (Q ◁ m) ≫ m := by
        rw [tensorHom_comp_whiskerLeft_assoc, hm, ← whiskerLeft_comp_tensorHom_assoc, hm]
      _ = ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ (Q ◁ m) ≫ m := by
        rw [associator_naturality_assoc]
  left_inv := by
    apply (cancel_epi q).1
    calc
      q ≫ lift v (𝟙 Q) ≫ m = lift (ι[A] ≫ q) q ≫ m := by
        have hh : q ≫ lift v (𝟙 Q) = lift (ι[A] ≫ q) q := by
          ext
          · simpa using hv
          · simp
        simpa only [Category.assoc] using congrArg (· ≫ m) hh
      _ = lift ι[A] (𝟙 A) ≫ (q ⊗ₘ q) ≫ m := by simp
      _ = lift ι[A] (𝟙 A) ≫ μ[A] ≫ q := by rw [hm]
      _ = q ≫ toUnit Q ≫ (η[A] ≫ q) := by
        rw [GrpObj.left_inv_assoc]
        simpa only [Category.assoc] using congrArg
          (fun f : A ⟶ 𝟙_ C => f ≫ η[A] ≫ q)
          (show toUnit A = q ≫ toUnit Q from toUnit_unique _ _)
  right_inv := by
    apply (cancel_epi q).1
    calc
      q ≫ lift (𝟙 Q) v ≫ m = lift q (ι[A] ≫ q) ≫ m := by
        have hh : q ≫ lift (𝟙 Q) v = lift q (ι[A] ≫ q) := by
          ext
          · simp
          · simpa using hv
        simpa only [Category.assoc] using congrArg (· ≫ m) hh
      _ = lift (𝟙 A) ι[A] ≫ (q ⊗ₘ q) ≫ m := by simp
      _ = lift (𝟙 A) ι[A] ≫ μ[A] ≫ q := by rw [hm]
      _ = q ≫ toUnit Q ≫ (η[A] ≫ q) := by
        rw [GrpObj.right_inv_assoc]
        simpa only [Category.assoc] using congrArg
          (fun f : A ⟶ 𝟙_ C => f ≫ η[A] ≫ q)
          (show toUnit A = q ≫ toUnit Q from toUnit_unique _ _)

/-- The original arrow is a homomorphism for the descended group structure. -/
theorem isMonHom_grpObjOfEpi :
    letI := grpObjOfEpi q m hm v hv
    IsMonHom q := by
  letI := grpObjOfEpi q m hm v hv
  exact ⟨rfl, hm.symm⟩

end Transport

variable {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (H : L1.FiniteStabilizerScheme A L) (Q : L1.StabilizerQuotient A L H)

/-- The actual quotient scheme receives a proved group-object structure. -/
@[reducible] def quotientGrp : GrpObj Q.Q :=
  let q := Q.q
  haveI : Epi q := epi_over_of_flat_surjective q
  have h₁ := tensor_fpqc (𝟙 (𝟙_ (Over (Spec (.of k))))) q
  haveI : Epi (𝟙 (𝟙_ (Over (Spec (.of k)))) ⊗ₘ q) :=
    letI := h₁.2.1
    letI := h₁.2.2
    epi_over_of_flat_surjective _
  have h₂ := tensor_fpqc q (𝟙 (𝟙_ (Over (Spec (.of k)))))
  haveI : Epi (q ⊗ₘ 𝟙 (𝟙_ (Over (Spec (.of k))))) :=
    letI := h₂.2.1
    letI := h₂.2.2
    epi_over_of_flat_surjective _
  have h₃ := tensor_fpqc q q
  haveI := h₃.1
  haveI := h₃.2.1
  haveI := h₃.2.2
  have h₄ := tensor_fpqc (q ⊗ₘ q) q
  haveI : Epi ((q ⊗ₘ q) ⊗ₘ q) :=
    letI := h₄.2.1
    letI := h₄.2.2
    epi_over_of_flat_surjective _
  grpObjOfEpi q (exists_quotientMul A L H Q).choose (exists_quotientMul A L H Q).choose_spec
    (exists_quotientInv A L H Q).choose (exists_quotientInv A L H Q).choose_spec

/-- The finite-flat quotient map is an actual homomorphism for the descended structure. -/
theorem quotient_isMonHom : letI := quotientGrp A L H Q; IsMonHom Q.q := by
  letI := quotientGrp A L H Q
  constructor
  · rfl
  · exact (exists_quotientMul A L H Q).choose_spec.symm

end ZInQ.Contrib.CloudR2Poincare.L4
