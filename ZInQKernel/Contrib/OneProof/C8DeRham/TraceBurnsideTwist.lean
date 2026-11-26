import ZInQKernel.Contrib.OneProof.C8DeRham.MatrixTraceSpan
import ZInQKernel.OneProof.H.TailB

/-!
# Trace comparison without a semisimplicity hypothesis on the witness

The comparison uses the actual `IsTwist` and `IsConj` of `HDec.G0Galois`.
At the attachment interface, the trace convention is arithmetic Frobenius,
as in `twistConj_of`. The coefficient embeddings and representations are inputs.
-/

namespace HDec.G0Galois

open _root_.PkgI4 (GaloisRep GaloisChar)

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- The repository's Burnside-form irreducibility transfers from `r` to `s` in the
same coordinates, with no semisimplicity hypothesis on `s`. -/
theorem isIrreducible_of_trace_eq_of_burnside (r s : GaloisRep ℓ n)
    (hirr : r.IsIrreducible) (htr : ∀ σ, (r.mat σ).trace = (s.mat σ).trace) :
    s.IsIrreducible :=
  _root_.ZInQ.MatrixTraceSpan.adjoin_eq_top_of_trace_eq r.toHom s.toHom htr hirr

/-- Use the proved matrix Brauer–Nesbitt theorem only after deriving both
semisimplicity facts from fullness. `IsConj r s` has orientation `r = P s P⁻¹`. -/
theorem isConj_of_trace_eq_of_burnside (r s : GaloisRep ℓ n)
    (hirr : r.IsIrreducible) (htr : ∀ σ, (r.mat σ).trace = (s.mat σ).trace) :
    IsConj r s := by
  have hs := isIrreducible_of_trace_eq_of_burnside r s hirr htr
  exact HSyn.t19_proved PkgI4.GQ (PadicAlgCl ℓ) n s.toHom r.toHom
    (isSemisimple_of_irreducible s hs) (isSemisimple_of_irreducible r hirr)
    (fun σ => (htr σ).symm)

/-- Compare to the supplied twist itself, not to a newly chosen twist or
semisimplification. The trace input is for the untwisted witness with the
scalar character inserted on the right. -/
theorem isConj_of_twisted_trace_eq (r ρ ρ' : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (hirr : r.IsIrreducible) (htw : IsTwist ρ' ψ ρ)
    (htr : ∀ σ, (r.mat σ).trace = (ψ.toHom σ : PadicAlgCl ℓ) * (ρ.mat σ).trace) :
    IsConj r ρ' := by
  apply isConj_of_trace_eq_of_burnside r ρ' hirr
  intro σ
  rw [htw σ, Matrix.trace_smul, smul_eq_mul]
  exact htr σ

/-- `twistConj_of`'s arithmetic-Frobenius attachment interface, with the
semisimplicity hypothesis on the attached representation removed. -/
theorem twistConj_of_burnside (r ρ ρ' : GaloisRep ℓ 2) (ψ : GaloisChar ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ}
    (g : PkgI4.CF N k) (S : Finset ℕ) (hN : 0 < N) (hirr : r.IsIrreducible)
    (hρatt : ρ.AttachedTo ιC ιL g) (hatt : r.AttachedUpToTwist ψ ιC ιL g S)
    (htw : IsTwist ρ' ψ ρ) : IsConj r ρ' := by
  have hNl : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  have htr := eq_of_eq_on_arithFrob (frobeniusDenseQ_of HSyn.frobeniusDense_proved)
    (S ∪ (N * ℓ).primeFactors) (fun x => (r.mat x).trace) (fun x => (ρ'.mat x).trace)
    (continuous_mat r).matrix_trace (continuous_mat ρ').matrix_trace (by
      intro p hp hpS v τ hv hτ
      have hpS' : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpN : ¬ p ∣ N * ℓ := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNl⟩))
      obtain ⟨-, α, hα, hαt⟩ := hatt p hp hpS'
      obtain ⟨-, α', hα', hα't⟩ := hρatt p hp hpN
      have hαα : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
      rw [hαt v τ hv hτ, htw τ, Matrix.trace_smul, hα't v τ hv hτ, hαα, smul_eq_mul])
  exact isConj_of_trace_eq_of_burnside r ρ' hirr (fun σ => congrFun htr σ)

end HDec.G0Galois
