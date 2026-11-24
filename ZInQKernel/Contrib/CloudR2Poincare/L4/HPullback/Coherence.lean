import ZInQKernel.Contrib.CloudR2Poincare.L4.HPullback.Composition

/-!
# Coherence for W07's EXISTING inverse-image constant-sheaf isomorphism

The composition/identity isomorphisms are the native adjunction mates from
Composition.lean. Mathlib's adjunction-composition associativity transports the
evident pushforward/evaluation-at-top coherence to this theta. The original W07
theta is used literally; no substitute inverse image or constant sheaf is defined.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
open CategoryTheory.Functor

namespace ZInQ.Contrib.CloudR2Poincare.L4.HPullback

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual pushforward/evaluation isomorphisms satisfy the required right-adjoint coherence. -/
theorem abelianPushforwardSectionsTopIso_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    isoWhiskerLeft (TopCat.Sheaf.pushforward AddCommGrpCat.{u} a.base)
        (abelianPushforwardSectionsTopIso b) ≪≫ abelianPushforwardSectionsTopIso a =
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (abelianPushforwardCompIso a b) (abelianSheafSectionsTop Z) ≪≫
        abelianPushforwardSectionsTopIso (a ≫ b) := by
  ext F
  simp [abelianPushforwardSectionsTopIso,
    Functor.sheafPushforwardContinuousCompSheafSectionsObjIso,
    abelianPushforwardCompIso]
  rfl

/-- The native integer theta respects composition under the canonical native inverse-image alpha. -/
theorem abelianInverseImageConstantIso_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    (Scheme.Modules.abelianInverseImage a).map
        (Scheme.Modules.abelianInverseImageConstantIso b).hom ≫
      (Scheme.Modules.abelianInverseImageConstantIso a).hom =
    (abelianInverseImageCompIso a b).hom.app (abelianConstantIntegerSheaf Z) ≫
      (Scheme.Modules.abelianInverseImageConstantIso (a ≫ b)).hom := by
  have h := Adjunction.leftAdjointCompIso_assoc
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u} isTerminalTop)
    (abelianInverseImageAdjunction b)
    (abelianInverseImageAdjunction a)
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop)
    (abelianInverseImageAdjunction (a ≫ b))
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)
    (abelianPushforwardSectionsTopIso b) (abelianPushforwardCompIso a b)
    (abelianPushforwardSectionsTopIso (a ≫ b)) (abelianPushforwardSectionsTopIso a)
    (abelianPushforwardSectionsTopIso_comp a b)
  rw [← abelianInverseImageConstantFunctorIso_eq_comp (a ≫ b),
      ← abelianInverseImageConstantFunctorIso_eq_comp b,
      ← abelianInverseImageConstantFunctorIso_eq_comp a] at h
  have hc := congrArg (fun e => e.hom.app (AddCommGrpCat.of (ULift.{u} ℤ))) h
  simpa [abelianInverseImageCompIso, abelianConstantIntegerSheaf,
    abelianInverseImageConstantFunctorIso, Scheme.Modules.abelianInverseImage,
    TopCat.Sheaf.pullback, Scheme.Modules.abelianInverseImageConstantIso] using hc.symm

/-- The native pushforward identity comparison is compatible with evaluation at top. -/
theorem abelianPushforwardSectionsTopIso_id (X : Scheme.{u}) :
    abelianPushforwardSectionsTopIso (𝟙 X) =
      isoWhiskerRight (abelianPushforwardIdIso X) (abelianSheafSectionsTop X) ≪≫
        Functor.leftUnitor (abelianSheafSectionsTop X) := by
  ext F
  simp [abelianPushforwardSectionsTopIso,
    Functor.sheafPushforwardContinuousCompSheafSectionsObjIso,
    abelianPushforwardIdIso]
  rfl

/-- W07's literal theta on the identity is the canonical native identity alpha. -/
theorem abelianInverseImageConstantIso_id (X : Scheme.{u}) :
    (Scheme.Modules.abelianInverseImageConstantIso (𝟙 X)).hom =
      (abelianInverseImageIdIso X).hom.app (abelianConstantIntegerSheaf X) := by
  have h := Adjunction.leftAdjointCompIso_comp_id
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)
    (abelianInverseImageAdjunction (𝟙 X))
    (abelianPushforwardSectionsTopIso (𝟙 X)) (abelianPushforwardIdIso X)
    (abelianPushforwardSectionsTopIso_id X)
  rw [← abelianInverseImageConstantFunctorIso_eq_comp (𝟙 X)] at h
  have hc := congrArg (fun e => e.hom.app (AddCommGrpCat.of (ULift.{u} ℤ))) h
  simpa [abelianInverseImageIdIso, abelianConstantIntegerSheaf,
    abelianInverseImageConstantFunctorIso, Scheme.Modules.abelianInverseImage,
    TopCat.Sheaf.pullback, Scheme.Modules.abelianInverseImageConstantIso] using hc

end ZInQ.Contrib.CloudR2Poincare.L4.HPullback
