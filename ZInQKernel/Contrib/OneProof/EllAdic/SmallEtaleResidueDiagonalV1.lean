import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleToProEtSiteV1
import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueConstantSheafV1
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

/-- Restrict the literal pro-étale residue sheaf on the small étale site.
In particular the sections are the same functions on the same schemes. -/
noncomputable def smallEtaleResidue (S : Scheme.{u}) (p n : ℕ) :
    S.Etaleᵒᵖ ⥤ Ab.{u+1} :=
  (smallEtaleToProEt S).op ⋙ (liftedFiniteResidueProEtTower S p).obj (op n)

/-- The diagonal uses the very same constant functions after restriction. -/
noncomputable def smallEtaleResidueDiagonal (S : Scheme.{u}) (p n : ℕ) :
    (Functor.const (S.Etale)ᵒᵖ).obj (liftedResidueCoefficient.{u} p n) ⟶
      smallEtaleResidue S p n :=
  Functor.whiskerLeft (smallEtaleToProEt S).op (liftedResidueConstantDiagonal S p n)

private theorem smallEtale_covering_of_jointlySurjective
    (S : Scheme.{u}) {U : S.Etale} {T : Sieve U}
    (h : ∀ x : U.left, ∃ (V : S.Etale) (f : V ⟶ U) (y : V.left),
      T f ∧ Etale f.left ∧ f.left y = x) : T ∈ S.smallEtaleTopology U := by
  let P : MorphismProperty Scheme.{u} := @Etale
  let : P.IsMultiplicative := inferInstanceAs (MorphismProperty.IsMultiplicative (@Etale : MorphismProperty Scheme.{u}))
  let : P.IsStableUnderComposition :=
    (inferInstance : P.IsMultiplicative).toIsStableUnderComposition
  have htop : S.smallEtaleTopology = (S.smallPretopology P P).toGrothendieck :=
    Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology S (P := P) (Q := P) le_rfl
  rw [htop]
  exact (Scheme.mem_toGrothendieck_smallPretopology (P := P) (Q := P) U T).2 h

/-- Every point has a lift over its actual open residue fibre, which is an
étale arrow even when the encompassing site is only the étale site. -/
theorem smallEtaleResidueDiagonal_locallySurjective (S : Scheme.{u}) (p n : ℕ) :
    Presheaf.IsLocallySurjective S.smallEtaleTopology (smallEtaleResidueDiagonal S p n) where
  imageSieve_mem {U} r := by
    change ULift.{u+1} (LocallyConstant U.left (ZMod (p ^ n))) at r
    apply smallEtale_covering_of_jointlySurjective S
    intro x
    let a : ZMod (p ^ n) := r.down x
    let V : U.left.Opens := ⟨{y | r.down y = a}, r.down.isLocallyConstant.isOpen_fiber a⟩
    let : Etale V.ι := inferInstance
    let : Etale U.hom := U.prop
    let W : S.Etale := Scheme.Etale.mk (V.ι ≫ U.hom)
    let f : W ⟶ U := MorphismProperty.Over.homMk V.ι rfl
    let y : W.left := ⟨x, rfl⟩
    refine ⟨W, f, y, ?_, (show Etale V.ι from inferInstance), rfl⟩
    change ∃ t : ULift.{u+1} (ZMod (p ^ n)),
      (smallEtaleResidueDiagonal S p n).app (op W) t = (smallEtaleResidue S p n).map f.op r
    refine ⟨ULift.up a, ?_⟩
    apply ULift.ext
    apply LocallyConstant.ext
    intro z
    change a = r.down (V.ι z)
    exact z.property.symm

/-- Evaluate the constants on any available point. If there is no point,
the empty family covers for the literal étale topology. -/
theorem smallEtaleResidueDiagonal_locallyInjective (S : Scheme.{u}) (p n : ℕ) :
    Presheaf.IsLocallyInjective S.smallEtaleTopology (smallEtaleResidueDiagonal S p n) where
  equalizerSieve_mem {U} x y h := by
    by_cases hu : Nonempty U.unop.left
    · obtain ⟨w⟩ := hu
      have hdown : x.down = y.down :=
        congrArg (fun z : ULift.{u+1} (LocallyConstant U.unop.left (ZMod (p ^ n))) => z.down w) h
      have heq : x = y := ULift.ext hdown
      subst y
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact S.smallEtaleTopology.top_mem U.unop
    · exact smallEtale_covering_of_jointlySurjective S (fun w => (hu ⟨w⟩).elim)

end RC53.EllAdic
