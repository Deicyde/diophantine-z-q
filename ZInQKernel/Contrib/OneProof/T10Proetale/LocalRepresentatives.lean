import ZInQKernel.Contrib.OneProof.T10Proetale.Tower
import ZInQKernel.Contrib.OneProof.T10Proetale.LiftTorsor
import ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover

/-!
# Local schemes representing the derived lift torsor

After a lift is chosen, the split cover represents the lifts over the slice.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

variable {X : Scheme.{0}} {B : Type} [TopologicalSpace B] [DiscreteTopology B]
  [AddCommGroup B] [IsTopologicalAddGroup B]

private abbrev coefficientPresentation (X : Scheme.{0}) (B : Type)
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] :=
  injectivePresentation (continuousCoefficients X B)

private abbrev quotientSections (X : Scheme.{0}) (B : Type)
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] :=
  (coefficientPresentation X B).X₃.obj.obj (op (T10Etale.terminalProEt X))

private abbrev geometricLiftSheaf (s : quotientSections X B) :=
  liftSheaf (S := coefficientPresentation X B) (T10Etale.isTerminalProEt X) s

/-- A chosen lift identifies the lifts over any object of the slice with the
maps over the base into its split cover. -/
def localLiftSections (s : quotientSections X B) {U V : X.ProEt}
    (x : (geometricLiftSheaf s).obj.obj (op U)) (f : V ⟶ U) :
    { p : V.left ⟶ (∐ fun _ : B => U.left) //
      p ≫ splitProjection U.left B = f.left } ≃ (geometricLiftSheaf s).obj.obj (op V) := by
  let h := T10Etale.isTerminalProEt X
  let y := (geometricLiftSheaf s).obj.map f.op x
  let e : ContinuousMap V.left B ≃ ULift.{1} (ContinuousMap V.left B) := Equiv.ulift.symm
  exact (splitSections (I := B) f.left).trans (e.trans
    (liftTrivialization (S := coefficientPresentation X B) h s
      (injectivePresentation_shortExact (continuousCoefficients X B)) y))

/-- The local representation is natural under precomposition in the slice
over the object where the lift is chosen. -/
theorem localLiftSections_restrict (s : quotientSections X B) {U V W : X.ProEt}
    (x : (geometricLiftSheaf s).obj.obj (op U)) (f : V ⟶ U) (k : W ⟶ V)
    (p : { p : V.left ⟶ (∐ fun _ : B => U.left) //
      p ≫ splitProjection U.left B = f.left }) :
    (geometricLiftSheaf s).obj.map k.op (localLiftSections s x f p) =
      localLiftSections s x (k ≫ f) ⟨k.left ≫ p.val, by
        calc
          (k.left ≫ p.val) ≫ splitProjection U.left B = k.left ≫ f.left := by
            rw [Category.assoc, p.2]
          _ = (k ≫ f).left := rfl⟩ := by
  let H := (geometricLiftSheaf s).obj
  let h := T10Etale.isTerminalProEt X
  let hS := injectivePresentation_shortExact (continuousCoefficients X B)
  let a : ULift.{1} (ContinuousMap V.left B) := ULift.up (splitSections f.left p)
  have eq := liftTrivialization_restrict (S := coefficientPresentation X B) h s hS k
    (H.map f.op x) a
  refine eq.trans ?_
  apply congrArg₂ (fun y b => liftTrivialization h s hS y b)
  · exact (Functor.map_comp_apply H f.op k.op x).symm
  · exact congrArg ULift.up (splitSections_restrict (I := B) f.left k.left p).symm

end
end ZInQ.Manuscript.T10Proetale
