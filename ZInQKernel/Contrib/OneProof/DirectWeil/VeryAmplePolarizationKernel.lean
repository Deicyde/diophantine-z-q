import ZInQKernel.Contrib.OneProof.DirectWeil.FiniteWeilPairing

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open PkgI3 PkgI3.AbVar HDec.WeilPairing T09Pic
open ZInQ.Contrib.CloudR2Poincare
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

/-- A very ample bundle over the ground field has a finite polarization kernel
on geometric points. -/
theorem finite_polarization_kernel_veryAmple {K : Type} [Field K]
    (A : AbVar K) (M : A.X.left.Modules) (hM : L2.VeryAmple A.X.hom M) :
    letI : M.IsInvertible := hM.isInvertible
    {x : A.Pt (AlgebraicClosure K) | polarization A (Scheme.Pic.mk M) x = 1}.Finite := by
  let : M.IsInvertible := hM.isInvertible
  let p := pullback.fst A.X.hom (ptK K).hom
  let N := (Scheme.Modules.pullback p).obj M
  have hN : L2.VeryAmple (AKbar A).X.hom N :=
    L2.veryAmple_abVar_baseChange (Ω := AlgebraicClosure K) A M hM
  let hNinv : N.IsInvertible := hN.isInvertible
  let c : (AK A).Pic := @Scheme.Pic.mk (AK A) N hNinv
  have hclass : bcPic A (Scheme.Pic.mk M) = c := Scheme.Pic.map_mk p M
  refine ((finite_kernel_veryAmple (AKbar A) N hN).preimage
    (f := pts (A := A)) pts_injective.injOn).subset ?_
  intro x hx
  change AC.phi (X := AKbar A) c (pts x) = 1
  change AC.phi (X := AKbar A) (bcPic A (Scheme.Pic.mk M)) (pts x) = 1 at hx
  rwa [← hclass]

/-- Every abelian variety admits a ground-field class with finite geometric polarization kernel. -/
theorem exists_finite_polarization_kernel {K : Type} [Field K] (A : AbVar K) :
    ∃ L : A.X.left.Pic, {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite := by
  obtain ⟨M, hM⟩ := exists_veryAmple A
  let : M.IsInvertible := hM.isInvertible
  exact ⟨Scheme.Pic.mk M, finite_polarization_kernel_veryAmple A M hM⟩

end PicDict.DirectPairing
