import ZInQKernel.Contrib.OneProof.EtaW32Character

/-! The target, copied verbatim from `ZInQKernel/Contrib/OneProof/CdOptimal/Level32.lean:56` (with `vC` from
line 46), and the check that the proved theorem has exactly that type. -/

open Complex CongruenceSubgroup
open scoped UpperHalfPlane MatrixGroups

namespace EtaW32Target

/-- `v(τ) = 1/w(τ) = η(8τ) η(32τ)² / η(16τ)³`. -/
noncomputable def vC (z : ℂ) : ℂ := ZInQ.Contrib.TYZGenus.X0.etaD 8 z * ZInQ.Contrib.TYZGenus.X0.etaD 32 z ^ 2 /
  ZInQ.Contrib.TYZGenus.X0.etaD 16 z ^ 3

def EtaW32Character : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 32 → ∀ τ : ℍ,
    vC ((γ • τ : ℍ) : ℂ) = ((ZMod.χ₈ ((γ 1 1 : ℤ) : ZMod 8) : ℤ) : ℂ) * vC τ

theorem same : EtaW32Character = ZInQ.CdOpt.EtaW32Character := rfl

theorem proved : EtaW32Character := ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof

end EtaW32Target

#print axioms EtaW32Target.proved
