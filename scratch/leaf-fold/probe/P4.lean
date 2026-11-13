import Mathlib
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.Contrib.LocalKW.T30
import ZInQKernel.Contrib.KroneckerWeber.Leaves
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense
import ZInQKernel.Contrib.Different.Global
import ZInQKernel.Contrib.T25.NewformOfEigenform
import ZInQKernel.Contrib.T31.Main
import ZInQKernel.HDecomp.Textbook.BrauerNesbitt

open scoped MatrixGroups ModularForm

namespace HDec.PkgI4
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f
end HDec.PkgI4

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let a := (env.find? `HDec.PkgI4.HasNebentypus).get!.value!.getUsedConstants
  let b := (env.find? `PkgI4.HasNebentypus).get!.value!.getUsedConstants
  logInfo m!"only HDec: {a.filter (fun c => !b.contains c)}\nonly root: {b.filter (fun c => !a.contains c)}"
