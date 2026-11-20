import ZInQKernel.Contrib.OneProof.T10Proetale.ResidueLimit
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# The difference sequence of the pro-étale coefficient tower

This is an actual short exact sequence of abelian sheaves. The epimorphism
in this sequence admits lifts on sections, using only the reduction maps of
the coefficient groups. Computing the cohomology of its middle terms is
a separate product issue.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped PadicInt

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe u

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- The coefficient sheaf at the finite level `n`. -/
abbrev residueSheaf (n : ℕ) := continuousCoefficients X (ZMod (ℓ ^ n))

/-- The coefficient sheaf of continuous functions into the product of the residue groups. -/
abbrev productSheaf := continuousCoefficients X (∀ n : ℕ, ZMod (ℓ ^ n))

/-- The projection on one residue. -/
def productProjection (n : ℕ) : productSheaf X ℓ ⟶ residueSheaf X ℓ n :=
  mapContinuousCoefficients X (Pi.evalRingHom _ n).toAddMonoidHom (continuous_apply n)

set_option backward.isDefEq.respectTransparency false in
private def productLift {F : Sheaf (Scheme.ProEt.topology X) Ab.{u+1}}
    (a : ∀ n, F ⟶ residueSheaf X ℓ n) : F ⟶ productSheaf X ℓ :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun x => ULift.up (ContinuousMap.pi fun n =>
            (a n).hom.app U x |>.down)
          map_zero' := ULift.ext (ContinuousMap.ext fun t => funext fun n =>
            congrArg (fun z : ULift.{u+1} C(U.unop.left, ZMod (ℓ ^ n)) => z.down t)
              (map_zero ((a n).hom.app U).hom))
          map_add' := fun x y => ULift.ext (ContinuousMap.ext fun t => funext fun n =>
            congrArg (fun z : ULift.{u+1} C(U.unop.left, ZMod (ℓ ^ n)) => z.down t)
              (map_add ((a n).hom.app U).hom x y)) }
      naturality := by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        funext n
        exact congrArg (fun z : ULift.{u+1} C(V.unop.left, ZMod (ℓ ^ n)) => z.down t)
          (NatTrans.naturality_apply (a n).hom f x) }

/-- The continuous-function sheaf of the product is the categorical product. -/
def productFanIsLimit : IsLimit (Fan.mk (productSheaf X ℓ) (productProjection X ℓ)) :=
  Fan.IsLimit.mk _ (fun s => productLift X ℓ s.proj)
    (by
      intro s n
      apply Sheaf.hom_ext
      ext U : 2
      rfl)
    (by
      intro s m hm
      apply Sheaf.hom_ext
      ext U : 2
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      apply ULift.ext
      apply ContinuousMap.ext
      intro y
      funext n
      exact congrArg (fun z : ULift.{u+1} C(U.unop.left, ZMod (ℓ ^ n)) => z.down y)
        (congrArg (fun q : s.pt ⟶ residueSheaf X ℓ n => q.hom.app U x) (hm n)))

private def difference : (∀ n : ℕ, ZMod (ℓ ^ n)) →+ ∀ n : ℕ, ZMod (ℓ ^ n) where
  toFun a n := a n - residueStep ℓ n (a (n + 1))
  map_zero' := funext fun n => by simp
  map_add' a b := funext fun n => by
    change a n + b n - residueStep ℓ n (a (n + 1) + b (n + 1)) = _
    rw [map_add]
    change _ = (a n - residueStep ℓ n (a (n + 1))) + (b n - residueStep ℓ n (b (n + 1)))
    abel

set_option backward.isDefEq.respectTransparency false in
/-- The difference operator of the tower as a map of sheaves. -/
def differenceHom : productSheaf X ℓ ⟶ productSheaf X ℓ :=
  mapContinuousCoefficients X (difference ℓ) (continuous_pi fun n =>
    (continuous_apply n).sub (continuous_of_discreteTopology.comp (continuous_apply (n + 1))))

/-- Every section has a preimage under the difference homomorphism. -/
theorem differenceHom_surjective_sections (U : X.ProEt) :
    Function.Surjective ((differenceHom X ℓ).hom.app (op U)) := by
  intro y
  let z : C(U.left, ∀ n : ℕ, ZMod (ℓ ^ n)) := y.down
  let a (n : ℕ) : C(U.left, ZMod (ℓ ^ n)) :=
    ⟨fun x => z x n, (continuous_apply n).comp z.continuous⟩
  let r (n : ℕ) (f : C(U.left, ZMod (ℓ ^ (n + 1)))) :
      C(U.left, ZMod (ℓ ^ n)) :=
    (⟨residueStep ℓ n, continuous_of_discreteTopology⟩ : C(_, _)).comp f
  have hr (n : ℕ) : Function.Surjective (r n) := by
    intro f
    obtain ⟨g, hg⟩ := residueStep_surjective_sections X ℓ n U (ULift.up f)
    exact ⟨g.down, congrArg ULift.down hg⟩
  obtain ⟨b, hb⟩ := difference_surjective r hr a
  refine ⟨ULift.up (ContinuousMap.pi b), ULift.ext (ContinuousMap.ext fun x => funext fun n => ?_)⟩
  exact congrArg (fun t : ∀ n, C(U.left, ZMod (ℓ ^ n)) => t n x) hb

/-- The difference map is already onto on sections, hence epi as a map of sheaves. -/
theorem differenceHom_epi : Epi (differenceHom X ℓ) := by
  let : Sheaf.IsLocallySurjective (differenceHom X ℓ) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun U =>
      differenceHom_surjective_sections X ℓ U.unop)
  infer_instance

variable [Fact ℓ.Prime]

/-- The integral coefficient map to the product, with the actual residue maps. -/
def integralToProduct : T10Etale.F X ℓ ⟶ productSheaf X ℓ :=
  mapContinuousCoefficients X (AddMonoidHom.pi fun n =>
    (PadicInt.toZModPow (p := ℓ) n).toAddMonoidHom)
    (continuous_pi fun n => continuous_toResidue ℓ n)

private theorem integralToProduct_injective_sections (U : X.ProEt) :
    Function.Injective ((integralToProduct X ℓ).hom.app (op U)) := by
  intro a b hab
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  exact PadicInt.ext_of_toZModPow.mp fun n =>
    congrArg (fun z : ULift.{u+1} C(U.left, ∀ n, ZMod (ℓ ^ n)) => z.down t n) hab

private theorem integralToProduct_zero : integralToProduct X ℓ ≫ differenceHom X ℓ = 0 := by
  apply Sheaf.hom_ext
  ext U : 2
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  funext n
  let z : C(U.unop.left, ℤ_[ℓ]) := a.down
  change PadicInt.toZModPow n (z t) - residueStep ℓ n (PadicInt.toZModPow (n + 1) (z t)) = 0
  exact sub_eq_zero.mpr (PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) (z t)).symm

/-- The difference short complex for the actual coefficient sheaf. -/
def coefficientSequence : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) :=
  ShortComplex.mk (integralToProduct X ℓ) (differenceHom X ℓ) (integralToProduct_zero X ℓ)

private lemma integralToProduct_lift_sections (U : X.ProEt)
    (b : (productSheaf X ℓ).obj.obj (op U))
    (hb : (differenceHom X ℓ).hom.app (op U) b = 0) :
    ∃ a, (integralToProduct X ℓ).hom.app (op U) a = b := by
  let z : C(U.left, ∀ n : ℕ, ZMod (ℓ ^ n)) := b.down
  let a (n : ℕ) : C(U.left, ZMod (ℓ ^ n)) :=
    ⟨fun x => z x n, (continuous_apply n).comp z.continuous⟩
  have hh (n : ℕ) (x : U.left) :
      residueStep ℓ n (a (n + 1) x) = a n x :=
    (sub_eq_zero.mp (congrArg (fun g : ULift.{u+1} C(U.left, ∀ n, ZMod (ℓ ^ n)) =>
      g.down x n) hb)).symm
  obtain ⟨f, hf, -⟩ := existsUnique_continuous_residueLift ℓ a hh
  exact ⟨ULift.up f, ULift.ext (ContinuousMap.ext fun x => funext fun n => hf n x)⟩

/-- The coefficient towers' difference sequence is short exact before cohomology. -/
theorem coefficientSequence_shortExact : (coefficientSequence X ℓ).ShortExact := by
  let S := coefficientSequence X ℓ
  let I := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u+1}
  have h₀ : IsLimit (KernelFork.ofι S.f S.zero) := by
    apply isLimitOfReflects I
    apply evaluationJointlyReflectsLimits
    intro U
    let E := I ⋙ (evaluation (X.ProEt)ᵒᵖ Ab.{u+1}).obj U
    let T := S.map E
    have hT : T.Exact ∧ Mono T.f := by
      refine ⟨T.ab_exact_iff.mpr ?_, (AddCommGrpCat.mono_iff_injective _).mpr ?_⟩
      · exact integralToProduct_lift_sections X ℓ U.unop
      · exact integralToProduct_injective_sections X ℓ U.unop
    exact (isLimitMapConeForkEquiv' E S.zero).symm
      (Classical.choice (T.exact_and_mono_f_iff_f_is_kernel.mp hT))
  exact
    { exact := (S.exact_and_mono_f_iff_f_is_kernel.mpr ⟨h₀⟩).1
      mono_f := (S.exact_and_mono_f_iff_f_is_kernel.mpr ⟨h₀⟩).2
      epi_g := differenceHom_epi X ℓ }


end
end ZInQ.Manuscript.T10Proetale
