import ZInQKernel.Contrib.CloudR2Poincare.L3.B2KernelBundle

/-!
# B1 applied to the actual rational restrictions of the Mumford bundle

The single square hypothesis is L2.NativeTheoremOfTheSquare. The B1
hypothesis remains an ordinary parameter. No statement here upgrades
closed-point fibre vanishing to universal direct-image vanishing without
the finite-free-complex/locality proof.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

/-- Translation invariance is closed under multiplication. -/
theorem TranslationInvariant.mul {k : Type u} [Field k] {B : PkgI3.AbVar k}
    {L N : B.X.left.Pic} (hL : TranslationInvariant B L) (hN : TranslationInvariant B N) :
    TranslationInvariant B (L * N) := by
  intro b
  rw [Scheme.Pic.map_mul, hL b, hN b]

/-- Translation invariance is closed under inversion. -/
theorem TranslationInvariant.inv {k : Type u} [Field k] {B : PkgI3.AbVar k}
    {N : B.X.left.Pic} (hN : TranslationInvariant B N) : TranslationInvariant B N⁻¹ := by
  intro b
  rw [L1.pic_map_inv, hN b]

/-- Any zero coefficient sheaf has zero native cohomology in every degree. -/
theorem subsingleton_native_H_of_isZero {X : Scheme.{u}} (F : X.Modules)
    (hF : IsZero F) (q : ℕ) : Subsingleton (F.H q) := by
  apply subsingleton_of_forall_eq 0
  intro z
  have H := congrArg (fun f : F ⟶ F => Scheme.Modules.H.map f q z)
    (hF.eq_of_src (𝟙 F) 0)
  simpa only [Scheme.Modules.H.map_id_apply, Scheme.Modules.H.map_zero_apply] using H

section Slices
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (M N : B.X.left.Modules) [M.IsInvertible] [N.IsInvertible]

/-- B1 supplies vanishing on each b×B if N is not in the polarization image. -/
theorem firstSlice_cohomology_vanish_of_not_in_image
    (hB1 : NativePicZeroVanishing.{u}) (hSquare : L2.NativeTheoremOfTheSquare.{u})
    (hN : TranslationInvariant B (Scheme.Pic.mk N))
    (hnot : ¬ ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X,
      Scheme.Pic.mk N = L1.translationClass B.X (Scheme.Pic.mk M) b)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) (q : ℕ) :
    Subsingleton (((Scheme.Modules.pullback (firstSlice B b).left).obj
      (mumfordKernelBundle B M N)).H q) := by
  let F := (Scheme.Modules.pullback (firstSlice B b).left).obj (mumfordKernelBundle B M N)
  have hclass : Scheme.Pic.mk F =
      L1.translationClass B.X (Scheme.Pic.mk M) b * (Scheme.Pic.mk N)⁻¹ := by
    rw [← Scheme.Pic.map_mk]
    exact mumfordKernelBundle_firstSlice_class B M N b
  have hI : TranslationInvariant B (Scheme.Pic.mk F) := by
    rw [hclass]
    exact TranslationInvariant.mul
      (L2.translationClass_invariant_of_nativeSquare hSquare B (Scheme.Pic.mk M) b) hN.inv
  have hne : Scheme.Pic.mk F ≠ 1 := by
    intro H
    rw [hclass] at H
    exact hnot ⟨b, (mul_inv_eq_one.mp H).symm⟩
  exact hB1 k B F hI hne q

/-- B1 supplies vanishing on B×b away from the actual translation stabilizer. -/
theorem secondSlice_cohomology_vanish_off_stabilizer
    (hB1 : NativePicZeroVanishing.{u}) (hSquare : L2.NativeTheoremOfTheSquare.{u})
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X)
    (hb : b ∉ L1.translationStabilizer B.X (Scheme.Pic.mk M)) (q : ℕ) :
    Subsingleton (((Scheme.Modules.pullback (secondSlice B b).left).obj
      (mumfordKernelBundle B M N)).H q) := by
  let F := (Scheme.Modules.pullback (secondSlice B b).left).obj (mumfordKernelBundle B M N)
  have hclass : Scheme.Pic.mk F = L1.translationClass B.X (Scheme.Pic.mk M) b := by
    rw [← Scheme.Pic.map_mk]
    exact mumfordKernelBundle_secondSlice_class B M N b
  have hI : TranslationInvariant B (Scheme.Pic.mk F) := by
    rw [hclass]
    exact L2.translationClass_invariant_of_nativeSquare hSquare B (Scheme.Pic.mk M) b
  have hne : Scheme.Pic.mk F ≠ 1 := by
    intro H
    rw [hclass] at H
    exact hb ((L1.translationClass_eq_one_iff B.X (Scheme.Pic.mk M) b).mp H)
  exact hB1 k B F hI hne q

/-- The actual coefficient restricted to B×0 has nonzero native H0. -/
theorem nontrivial_H_zero_secondSlice (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible] :
    Nontrivial (((Scheme.Modules.pullback
      (secondSlice B (1 : 𝟙_ (Over (Spec (.of k))) ⟶ B.X)).left).obj
      (mumfordKernelBundle B M N)).H 0) := by
  obtain ⟨e⟩ := mumfordKernelBundle_zeroSlice_iso B M N
  let U : B.X.left.Modules := SheafOfModules.unit B.X.left.ringCatSheaf
  let eg : Γ(B.X.left, ⊤) ≃ k :=
    (Equiv.ofBijective B.X.hom.appTop
      (AlgebraicGeometry.bijective_appTop_of_isProper_of_geometricallyIntegral B.X.hom)).symm.trans
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toEquiv
  haveI : Nontrivial Γ(B.X.left, ⊤) := eg.nontrivial
  haveI : Nontrivial Γ(U, ⊤) := inferInstanceAs (Nontrivial Γ(B.X.left, ⊤))
  haveI : Nontrivial (U.H 0) := (Scheme.Modules.H.zeroLinearEquiv U).toEquiv.nontrivial
  exact (Scheme.Modules.H.mapLinearEquiv (show _ ≅ U from e) 0).toEquiv.nontrivial

end Slices
end ZInQ.Contrib.CloudR2Poincare.L3
