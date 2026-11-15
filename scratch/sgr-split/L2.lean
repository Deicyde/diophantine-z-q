import ZInQKernel.OneProof.H.TailZ16
import ZInQKernel.Contrib.AbVarBC.Main

noncomputable section

namespace SGRL2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- L2 in characteristic 0. -/
def AbVarEndTorsionFree0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : PkgI3.AbVar K) (n : ℕ) (f : PkgI3.AbVar.End A),
    0 < n → n • f = 0 → f = 0

theorem abVarEndTorsionFree0 : AbVarEndTorsionFree0 := by
  intro K _ _ A n f hn h
  obtain ⟨-, hsurj⟩ := ZInQ.Contrib.AbVarBC.mulIsogeny K A (n : ℤ) (by exact_mod_cast hn.ne')
  have h1 : f * ((n : ℤ) : PkgI3.AbVar.End A) = 0 := by
    rw [← Int.cast_comm, ← zsmul_eq_mul, natCast_zsmul, h]
  have h2 : ((n : ℤ) : PkgI3.AbVar.End A).hom ≫ f.hom =
      ((n : ℤ) : PkgI3.AbVar.End A).hom ≫ (1 : A.X ⟶ A.X) := by
    rw [MonObj.comp_one]
    exact congrArg PkgI3.AbVar.Hom.hom h1
  apply PkgI3.AbVar.Hom.ext'
  rw [PkgI3.AbVar.Hom.hom_zero]
  apply Over.OverMorphism.ext
  have : IsReduced A.X.left := LeafQM.AV.R1UnivRigid.isReduced_of_smooth A.X.hom
  have : IsDominant ((n : ℤ) : PkgI3.AbVar.End A).hom.left := inferInstance
  exact ext_of_isDominant_of_isSeparated A.X.hom (by rw [Over.w, Over.w])
    ((n : ℤ) : PkgI3.AbVar.End A).hom.left (by rw [← Over.comp_left, h2, Over.comp_left])

end SGRL2

#print axioms SGRL2.abVarEndTorsionFree0
