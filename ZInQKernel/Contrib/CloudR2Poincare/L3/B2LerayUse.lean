import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Leray
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2SliceVanishing

/-! The two native Leray uses, with finite support kept as the single labelled
input. No global-H or projection-switch assumption is manufactured. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u

/-- All direct images zero imply all actual native global cohomology zero. -/
theorem native_global_H_zero_of_higherDirectImages_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules)
    (hR : ∀ j : ℕ, IsZero ((Scheme.Modules.higherDirectImage f j).obj F)) (i : ℕ) :
    Subsingleton (F.H i) := by
  have hacyc : ∀ j p : ℕ, 0 < p →
      Subsingleton (((Scheme.Modules.higherDirectImage f j).obj F).H p) :=
    fun j p _ => subsingleton_native_H_of_isZero _ (hR j) p
  obtain ⟨e⟩ := nonempty_native_leray_addEquiv f F hacyc i
  haveI := subsingleton_native_H_of_isZero _ (hR i) 0
  exact e.toEquiv.subsingleton

/-- The two Leray applications force every p2 direct image to vanish once the
actual p1 direct images vanish and the p2 sheaves have genuine finite support. -/
theorem higherDirectImages_snd_zero_of_fst_zero_finite_support
    (hfiniteSupport : FiniteSupportCohomology.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (F : (B.X ⊗ B.X).left.Modules) [F.IsQuasicoherent]
    (hfst : ∀ j : ℕ, IsZero ((Scheme.Modules.higherDirectImage (fst B.X B.X).left j).obj F))
    (S : Set B.X.left) (hS : S.Finite) (hClosed : ∀ y ∈ S, IsClosed ({y} : Set B.X.left))
    (hsupport : ∀ j : ℕ, ∀ y : B.X.left, y ∉ S →
      Subsingleton (((Scheme.Modules.higherDirectImage (snd B.X B.X).left j).obj F).presheaf.stalk y)) :
    ∀ i : ℕ, IsZero ((Scheme.Modules.higherDirectImage (snd B.X B.X).left i).obj F) := by
  let f := (snd B.X B.X).left
  haveI : QuasiCompact f := inferInstanceAs (QuasiCompact (pullback.snd B.X.hom B.X.hom))
  haveI : IsSeparated f := inferInstanceAs (IsSeparated (pullback.snd B.X.hom B.X.hom))
  haveI (j : ℕ) : ((Scheme.Modules.higherDirectImage f j).obj F).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_higherDirectImage f F j
  have hacyc : ∀ j p : ℕ, 0 < p →
      Subsingleton (((Scheme.Modules.higherDirectImage f j).obj F).H p) :=
    fun j => (hfiniteSupport k B _ S hS hClosed (hsupport j)).1
  intro i
  haveI : Subsingleton (F.H i) :=
    native_global_H_zero_of_higherDirectImages_zero (fst B.X B.X).left F hfst i
  obtain ⟨e⟩ := nonempty_native_leray_addEquiv f F hacyc i
  haveI : Subsingleton (((Scheme.Modules.higherDirectImage f i).obj F).H 0) :=
    e.symm.toEquiv.subsingleton
  exact (hfiniteSupport k B _ S hS hClosed (hsupport i)).2 inferInstance

end ZInQ.Contrib.CloudR2Poincare.L3
