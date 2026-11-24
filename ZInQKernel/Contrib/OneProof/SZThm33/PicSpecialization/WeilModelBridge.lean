import ZInQKernel.Contrib.OneProof.DirectWeil.FiniteWeilPairing
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.WeilSpecialization

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open Scheme.Modules
open PkgI3 PkgI3.AbVar HDec.WeilPairing T09Pic
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

open Transport

/-- The finite pairing is computed by the Weil formula for any actual line
bundle in the right Picard class, with any trivialization of its multiplication pullback. -/
theorem wf_eq_const_value_of_pic_mk {K : Type} [Field K] (A : AbVar K)
    (L : A.X.left.Pic) {n : ℕ} (hn : 0 < n) (hchar : (n : K) ≠ 0)
    (x y : tors A n) (M : (AK A).Modules) [M.IsInvertible]
    (hM : Scheme.Pic.mk M = torsionClass A L y)
    (ψ : unit (AK A) ≅ (Scheme.Modules.pullback (mlN A n)).obj M) :
    wf (trl (Additive.toMul (x : P A))) (mlN A n) (transl_left_comp_mulN_left x) M ψ =
      constK A (value A L hn hchar x y : AlgebraicClosure K) := by
  let c := torsionClass A L y
  have hM' : Scheme.Pic.mk M = Scheme.Pic.mk (mod c) :=
    hM.trans (Scheme.Pic.mk_fromSkeleton c).symm
  obtain ⟨e⟩ := (Scheme.Pic.mk_eq_mk_iff _ _).mp hM'
  let ψ' : Triv A n c := ψ ≪≫ (Scheme.Modules.pullback (mlN A n)).mapIso e
  rw [value_spec A L hn hchar x y ψ', weilFormula_eq_wf]
  exact (wf_iso _ _ _ e ψ).symm

end PicDict.DirectPairing
