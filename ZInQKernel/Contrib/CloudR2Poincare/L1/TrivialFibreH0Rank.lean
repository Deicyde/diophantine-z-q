import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedKernelSplit
import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeTrivialityLocus
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PushforwardUnit

/-! Actual proper geometrically-integral fibre triviality gives H0 rank ONE,
not just nontrivial global sections. This supplies the genuine dimension
premise of the reduced constant-rank/Grauert argument. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- A trivial bundle on a proper geometrically integral scheme over a field has
actual degree-zero higher-direct-image dimension exactly one. -/
theorem finrank_higherDirectImage_zero_eq_one_of_iso_unit
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] (M : X.Modules)
    (eM : M ≅ Scheme.Modules.unit X) :
    Module.finrank k ((moduleSpecΓFunctor (R := .of k)).obj
      ((Scheme.Modules.higherDirectImage f 0).obj M)) = 1 := by
  let E := moduleSpecΓFunctor (R := CommRingCat.of k)
  let er := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  let eu : k ≃ₗ[k] E.obj (Scheme.Modules.unit (Spec (.of k))) :=
    { er.toAddEquiv with
      map_smul' := fun c x ↦ by
        change er (c * x) = (Scheme.ΓSpecIso (.of k)).inv c * er x
        exact er.map_mul c x }
  let u := E.map (AlgebraicGeometry.pushforwardUnitMap f)
  have hu : Function.Bijective u.hom := by
    change Function.Bijective (Scheme.Modules.Hom.app (AlgebraicGeometry.pushforwardUnitMap f) ⊤)
    have hfun : ((Scheme.Modules.Hom.app (AlgebraicGeometry.pushforwardUnitMap f) ⊤) :
        Γ(Spec (.of k), ⊤) → Γ(X, ⊤)) = f.appTop :=
      funext (AlgebraicGeometry.pushforwardUnitMap_app f ⊤)
    rw [hfun]
    exact AlgebraicGeometry.bijective_appTop_of_isProper_of_geometricallyIntegral f
  let ep := LinearEquiv.ofBijective u.hom hu
  let ez := (E.mapIso ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.app
    (Scheme.Modules.unit X))).toLinearEquiv
  let em := (E.mapIso ((Scheme.Modules.higherDirectImage f 0).mapIso eM)).toLinearEquiv
  calc
    Module.finrank k (E.obj ((Scheme.Modules.higherDirectImage f 0).obj M)) =
        Module.finrank k (E.obj ((Scheme.Modules.higherDirectImage f 0).obj (Scheme.Modules.unit X))) :=
      em.finrank_eq
    _ = Module.finrank k (E.obj ((Scheme.Modules.pushforward f).obj (Scheme.Modules.unit X))) :=
      ez.finrank_eq
    _ = Module.finrank k (E.obj (Scheme.Modules.unit (Spec (.of k)))) := ep.finrank_eq.symm
    _ = Module.finrank k k := eu.finrank_eq.symm
    _ = 1 := Module.finrank_self k

/-- Actual triviality of every residue fibre supplies the original H0 rank-one
hypothesis, under properness and geometric integrality of the family. -/
theorem residueRank_zero_eq_one_of_trivial_fibres
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hM : ∀ y : Y, Scheme.Pic.map (pullback.fst f (Y.fromSpecResidueField y)) (Scheme.Pic.mk M) = 1) :
    ∀ y : Y, higherDirectImageResidueRank f M 0 y = 1 := by
  intro y
  obtain ⟨e⟩ := (fibrePicardClass_eq_one_iff_iso f M y).mp (hM y)
  exact finrank_higherDirectImage_zero_eq_one_of_iso_unit (pullback.snd f (Y.fromSpecResidueField y))
    ((Scheme.Modules.pullback (pullback.fst f (Y.fromSpecResidueField y))).obj M) e

end ZInQ.Contrib.CloudR2Poincare.L1
