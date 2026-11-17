import ZInQKernel.Contrib.OneProof.HodgeTateDecompAbVarDecomp
import ZInQKernel.Contrib.OneProof.HodgeTateDecompAbVarWeil

/-!
# The Hodge–Tate decomposition of `V_p(A)`, part 3: the multiplicities are `g` and `g`

Task hodgetate-from-dr (2026-11-16; report `docs/research/hodgetate-from-dr.md`).

From the leaf `HodgeTateDecompExists` (`ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^a ⊕ ℂ_p^b`, Fontaine's decomposition with
bases chosen) the field `HodgeSplit.HodgeTateDecompAbVar` (the same with `a = b = g = dim A`) follows:

* `a = b`: the `p`-adic Weil pairing on `V_p(A)` (`tateGSp_field`, from T9, the isogeny quasi-inverse and T5)
  is nondegenerate with multiplier the cyclotomic character, and `eq_of_pairing` counts
  `Hom_{G_F}(V, ℂ_p(1))` in two ways with Tate's two theorems;
* `a + b = dim V_p(A) = 2g` (T26 from T5, inside `tateGSp_field`).

`cyclotomicCharacter_eq_of_comm` identifies the multiplier (Mathlib's cyclotomic character of `F̄`) with
pkg-I4's `cyc` on `ℚ̄_p` along `gfToGqp`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace ZInQ.Contrib.HodgeTateFromPairing

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-! ## §2. The field from the leaf -/

/-- pkg-I4's abelian variety as the kernel's `PkgI3.AbVar` (same scheme; `V_p` and the Galois action
agree definitionally, as in `AbVarBC.vToI4`). -/
def toK' (F : Type) [Field F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : _root_.PkgI3.AbVar F :=
  @_root_.PkgI3.AbVar.mk F _ A.X A.grp A.proper A.smooth A.geomInt

set_option maxHeartbeats 3000000 in
/-- - the leaf `HodgeTateDecompExists`**, Tate's two theorems, and the
inputs of the Weil pairing: T9 (`T09_SymmIsogenyExists`), the isogeny quasi-inverse, and T5. -/
theorem testA (hHT : HodgeTateDecompExists) (hT : TateTwistInvariants)
    (hA : AxSenTate) (h9 : HDec.WeilPairing.T09_SymmIsogenyExists)
    (hQ : HDec.WeilPairing.IsogenyQuasiInverse) (hT5 : HDec.PkgI2.TorsionStructure.{0}) :
    HodgeTateDecompAbVar := by
  intro p _ F _ _ _ A g hg
  obtain ⟨X⟩ := A
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  have : NeZero (p : F) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  let A' : _root_.PkgI3.AbVar F := ⟨X⟩
  -- work with `A'' = toI4 A'`, which is `A` up to structure eta
  have key : ∃ e : ℂ_[p] ⊗[ℚ_[p]] (ZInQ.Contrib.AbVarBC.toI4 A').V p ≃ₗ[ℂ_[p]]
      (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] (ZInQ.Contrib.AbVarBC.toI4 A').V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) ((ZInQ.Contrib.AbVarBC.toI4 A').galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))) := by
    sorry
    obtain ⟨a, b, e, he⟩ := hHT p F (ZInQ.Contrib.AbVarBC.toI4 A')
    obtain ⟨hfd, B, hrank, hnd, -, hmult⟩ := tateGSp_field h9 hQ hT5 F A' p g hg
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

set_option maxHeartbeats 3000000 in
/-- - the leaf `HodgeTateDecompExists`**, Tate's two theorems, and the
inputs of the Weil pairing: T9 (`T09_SymmIsogenyExists`), the isogeny quasi-inverse, and T5. -/

example (F : Type) [Field F] (p : ℕ) [Fact p.Prime] (X : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    (ZInQ.Contrib.AbVarBC.toI4 (toK' F X)).V p = X.V p := rfl

end

end ZInQ.Contrib.HodgeTateFromPairing
