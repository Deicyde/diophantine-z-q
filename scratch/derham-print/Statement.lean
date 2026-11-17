import ZInQKernel.OneProof.H.TailS

/-! # derham-print: the field `deRhamH1AbVarT`, copied verbatim

`ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` and what it depends on (`ddrTensorOver`, `IsDeRhamTensorOver`), copied
verbatim from `ZInQKernel/OneProof/H/TailS.lean` (lines 1970-1994 at 5e235a40) into a fresh namespace; the
`example`s check that the copies are the original constants up to `rfl`. -/

set_option linter.unusedSectionVars false

namespace DerhamPrintCopy

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `D_dR,F(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}`. -/
def ddrTensorOver {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] W) where
  carrier := {x | ∀ σ, TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c x hx σ := by rw [map_smul, hx σ]

/-- **`W` is de Rham over `F`** in the printed sense: `dim_F (B_dR ⊗ W)^{G_F} = dim W`. -/
def IsDeRhamTensorOver {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) : Prop :=
  Module.finrank ℚ_[p] (ddrTensorOver p ρW) = Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] W

/-- **LEAF (the de Rham comparison for `H¹` of an abelian variety, printed `D_dR`).** As
`DeRhamH1AbVar`, with `H¹_ét(A_{F̄}, ℚ_p)` replaced by `Hom_{ℚ_p}(V_p(A), ℚ_p)` with the
contragredient action (the standard identification; Milne, *Abelian varieties*, Thm 15.1(a),
UNVERIFIED) and `D_dR` in its printed form `(B_dR ⊗ W)^{G_F}`. Faltings 1989; Tsuji 1999; Scholze,
Forum Math. Pi 1 (2013), Cor. 1.8; Fontaine 1982 for abelian varieties. -/
def DeRhamH1AbVarT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), IsDeRhamTensorOver p (A.galRep p).dual

end

end DerhamPrintCopy

example (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    DerhamPrintCopy.ddrTensorOver p ρW = ZInQ.Contrib.HodgeSplit.ddrTensorOver p ρW := rfl

example : DerhamPrintCopy.DeRhamH1AbVarT ↔ ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT := Iff.rfl
