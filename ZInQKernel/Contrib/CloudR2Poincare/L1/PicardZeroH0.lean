import ZInQKernel.Contrib.CloudR2Poincare.L1.SectionsTriviality
import ZInQKernel.HDecomp.Objects

/-!
# Native H^0 vanishing from the inverse-pullback identity

H-72 L1 continuation (B). Once the multiplicative/seesaw argument supplies
[-1]^*N = N^{-1} in the ACTUAL Picard group, a nonzero global section of N
would also give a nonzero global section of N^{-1}; native seesaw then makes N
trivial. The inverse-pullback identity is an explicit ordinary argument, not
installed as a desired Picard-zero Fact. L2 owns its anti-diagonal derivation;
L1 owns this cohomology consequence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite MonoidalCategory AlgebraicGeometry
open scoped MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- An actual isomorphism of schemes preserves nonzero global sections under pullback. -/
theorem nontrivial_globalSections_pullback_of_isIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (M : X.Modules)
    [Nontrivial Γ(M, ⊤)] : Nontrivial Γ((Modules.pullback f).obj M, ⊤) := by
  have hRange : (⊤ : X.Opens) ≤ f.opensRange := by
    intro x hx
    exact ⟨(inv f) x, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl⟩
  have hbij := Modules.bijective_pullbackUnit_app_of_isOpenImmersion f M hRange
  let e : Γ(M, ⊤) ≃ Γ((Modules.pullback f).obj M, ⊤) :=
    Equiv.ofBijective (Modules.pullbackΓ f M) (by
      rw [Modules.pullbackΓ_def]
      exact hbij)
  exact e.symm.nontrivial

/-- The first B-vanishing consequence: an ACTUAL nontrivial bundle with inverse
pullback symmetry has no global sections. -/
theorem subsingleton_globalSections_of_inversePullback
    {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k)
    (N : A.X.left.Modules) [N.IsInvertible]
    (hN : Pic.mk N ≠ 1)
    (hInv : Pic.map ι[A.X].left (Pic.mk N) = (Pic.mk N)⁻¹) :
    Subsingleton Γ(N, ⊤) := by
  classical
  rcases subsingleton_or_nontrivial Γ(N, ⊤) with hzero | hnonzero
  · exact hzero
  · haveI := hnonzero
    haveI : IsIso ι[A.X].left := inferInstanceAs (IsIso ((Over.forget _).map ι[A.X]))
    haveI : Nontrivial Γ((Modules.pullback ι[A.X].left).obj N, ⊤) :=
      nontrivial_globalSections_pullback_of_isIso ι[A.X].left N
    have hdual : Pic.mk ((Modules.pullback ι[A.X].left).obj N) = Pic.mk Nᵛ := by
      rw [← Pic.map_mk, Pic.mk_dual]
      exact hInv
    obtain ⟨e⟩ := (Pic.mk_eq_mk_iff _ _).mp hdual
    haveI : Nontrivial Γ(Nᵛ, ⊤) := (Modules.appLinearEquivOfIso e ⊤).toEquiv.symm.nontrivial
    obtain ⟨trivial⟩ := (nonempty_iso_unit_iff_nontrivial_globalSections A.X.hom N).mpr
      ⟨inferInstance, inferInstance⟩
    exact (hN ((Pic.mk_eq_mk_iff _ _).mpr ⟨trivial⟩)).elim

/-- The ACTUAL native sheaf-cohomology group H^0 is zero under the same input. -/
theorem subsingleton_H_zero_of_inversePullback
    {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k)
    (N : A.X.left.Modules) [N.IsInvertible]
    (hN : Pic.mk N ≠ 1)
    (hInv : Pic.map ι[A.X].left (Pic.mk N) = (Pic.mk N)⁻¹) :
    Subsingleton (N.H 0) := by
  haveI := subsingleton_globalSections_of_inversePullback A N hN hInv
  exact (Modules.H.zeroLinearEquiv N).toEquiv.subsingleton

end ZInQ.Contrib.CloudR2Poincare.L1
