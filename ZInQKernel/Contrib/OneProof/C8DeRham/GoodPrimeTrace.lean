import ZInQKernel.Contrib.OneProof.C8Printed

/-! # Comparison at the actual good-prime eigensystem -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep GaloisChar)

set_option maxHeartbeats 1500000 in
/-- No semisimplicity is used to compare the characters of the actual
Pan representation and the scalar twist of the modular witness. -/
theorem trace_eq_of_attached_twist
    (hD : HSyn.FrobeniusDense) (r ρ ρ' : GaloisRep 5 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (N : ℕ) {k : ℤ}
    (g : PkgI4.CF N k) (S : Finset ℕ) (hN : 0 < N) (hρatt : ρ.AttachedTo ιC ιL g)
    (hatt : r.AttachedUpToTwist ψ ιC ιL g S) (htw : IsTwist ρ' ψ ρ) :
    ∀ σ, (r.mat σ).trace = (ρ'.mat σ).trace := by
  have hN' : N * 5 ≠ 0 := Nat.mul_ne_zero hN.ne' (by decide)
  have ht := C9Rhof.eq_of_eq_on_arithFrob (frobeniusDenseQ_of hD) (S ∪ (N * 5).primeFactors)
    (fun σ => (r.mat σ).trace) (fun σ => (ρ'.mat σ).trace)
    (TwistHT.continuous_trace_mat r) (TwistHT.continuous_trace_mat ρ') (by
      intro q hq hqS v σ hv hσ
      have hs : q ∉ S := fun h => hqS (Finset.mem_union_left _ h)
      have hp : ¬ q ∣ N * 5 := fun h => hqS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hq, h, hN'⟩))
      obtain ⟨_, a, ha, ht⟩ := hatt q hq hs
      obtain ⟨_, b, hb, ht'⟩ := hρatt q hq hp
      have hab := ιC.injective (ha.trans hb.symm)
      rw [ht v σ hv hσ, htw σ, Matrix.trace_smul, ht' v σ hv hσ, hab, smul_eq_mul])
  exact fun σ => congrFun ht σ

end HDec.G0Galois.C8Conrad.Manuscript
