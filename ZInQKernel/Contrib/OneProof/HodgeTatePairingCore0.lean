import ZInQKernel.Contrib.OneProof.HodgeTatePairingDecomp
import ZInQKernel.Contrib.OneProof.HodgeTatePairingWeil0

/-!
# The Hodge–Tate decomposition of `V_p(A)` from the characteristic-`0` T9

Task fold34-ht (2026-11-16). `HodgeTatePairingCore.lean` (hodgetate-from-dr) verbatim, with T9 in its
characteristic-`0` form (the type of `PicZeroChar0.T09_SymmIsogenyExists0`, written out): the base field `F` is
finite over `ℚ_p`, hence of characteristic `0`, and the proof applies T9 only at `F` (through `tateGSp_field0`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace ZInQ.Contrib.HodgeTateFromPairing

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-! ## §2. The field from the leaf -/

set_option maxHeartbeats 1000000 in
/-- **`HodgeTateDecompAbVar` from the leaf `HodgeTateDecompExists`**, Tate's two theorems, and the
inputs of the Weil pairing: T9 in characteristic `0` (the type of `PicZeroChar0.T09_SymmIsogenyExists0`), the
isogeny quasi-inverse, and T5. -/
theorem hodgeTateDecompAbVar_of_leaves0 (hHT : HodgeTateDecompExists) (hT : TateTwistInvariants)
    (hA : AxSenTate) (h9 : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K),
      Nonempty (HDec.WeilPairing.SymmIsogeny A))
    (hQ : HDec.WeilPairing.IsogenyQuasiInverse) (hT5 : HDec.PkgI2.TorsionStructure.{0}) :
    HodgeTateDecompAbVar := by
  intro p _ F _ _ _ A g hg
  obtain ⟨X⟩ := A
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  have : NeZero (p : F) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  let A' : _root_.PkgI3.AbVar F := ⟨X⟩
  -- `toI4 A'` is `A` (after the case split, by unfolding)
  have key : ∃ e : ℂ_[p] ⊗[ℚ_[p]] (ZInQ.Contrib.AbVarBC.toI4 A').V p ≃ₗ[ℂ_[p]]
      (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] (ZInQ.Contrib.AbVarBC.toI4 A').V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) ((ZInQ.Contrib.AbVarBC.toI4 A').galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))) := by
    obtain ⟨a, b, e, he⟩ := hHT p F (ZInQ.Contrib.AbVarBC.toI4 A')
    obtain ⟨hfd, B, hrank, hnd, -, hmult⟩ := tateGSp_field0 h9 hQ hT5 F A' p g hg
    let w := ZInQ.Contrib.AbVarBC.vToI4 p A'
    have : FiniteDimensional ℚ_[p] ((ZInQ.Contrib.AbVarBC.toI4 A').V p) :=
      LinearEquiv.finiteDimensional w.symm
    let B' : LinearMap.BilinForm ℚ_[p] ((ZInQ.Contrib.AbVarBC.toI4 A').V p) :=
      LinearMap.BilinForm.congr w.symm B
    have hB' : ∀ x y, B' x y = B (w x) (w y) := fun x y => by
      rw [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_symm]
    have hnd' : B'.Nondegenerate := (LinearMap.BilinForm.nondegenerate_congr_iff w.symm).2 hnd
    have hmult' : ∀ σ x y, B' ((ZInQ.Contrib.AbVarBC.toI4 A').galRep p σ x)
        ((ZInQ.Contrib.AbVarBC.toI4 A').galRep p σ y) = cycPow p (gfToGqp p F σ) 1 * B' x y := by
      intro σ x y
      rw [hB', hB', ZInQ.Contrib.AbVarBC.vToI4_galRep, ZInQ.Contrib.AbVarBC.vToI4_galRep,
        cycPow_gfToGqp_one]
      exact hmult σ (w x) (w y)
    have hab : a = b := eq_of_pairing p _ B' hnd' hmult' e he hT hA
    have hsum : a + b = Module.finrank ℚ_[p] ((ZInQ.Contrib.AbVarBC.toI4 A').V p) :=
      add_eq_finrank p e
    rw [w.finrank_eq, hrank] at hsum
    have ha : a = g := by omega
    have hb : b = g := by omega
    subst ha hb
    exact ⟨e, he⟩
  exact key

end

end ZInQ.Contrib.HodgeTateFromPairing

#print axioms ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_leaves0
