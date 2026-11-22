import ZInQKernel.Contrib.OneProof.TateSemisimplicity

/-! # Rational comparison maps for homomorphisms of abelian varieties -/

noncomputable section
open PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

variable {K : Type} [Field K] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The natural scalar extension of the Tate map to rational Tate spaces. -/
def tateHomQl (A B : PkgI3.AbVar K) :
    ℚ_[ℓ] ⊗[ℤ] Hom A B →ₗ[ℤ] (A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) :=
  TensorProduct.lift <| LinearMap.mk₂ ℤ (fun (a : ℚ_[ℓ]) (f : Hom A B) => a • (homT (ℓ := ℓ) f).baseChange ℚ_[ℓ])
    (fun a b _ => add_smul a b _)
    (fun n a _ => by rw [smul_assoc])
    (fun a f g => by
      change a • (tateHom ℓ A B (f + g)).baseChange ℚ_[ℓ] =
        a • (tateHom ℓ A B f).baseChange ℚ_[ℓ] + a • (tateHom ℓ A B g).baseChange ℚ_[ℓ]
      rw [map_add, LinearMap.baseChange_add, smul_add])
    (fun n a f => by
      change a • (tateHom ℓ A B (n • f)).baseChange ℚ_[ℓ] =
        n • (a • (tateHom ℓ A B f).baseChange ℚ_[ℓ])
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℤ_[ℓ], LinearMap.baseChange_smul]
      let h := (tateHom ℓ A B f).baseChange ℚ_[ℓ]
      have hn : (n : ℤ_[ℓ]) • h = n • h := Int.cast_smul_eq_zsmul ℤ_[ℓ] n h
      exact (congrArg (fun v : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ => a • v) hn).trans (smul_comm a n h))

theorem tateHomQl_tmul (A B : PkgI3.AbVar K) (a : ℚ_[ℓ]) (f : Hom A B) :
    tateHomQl ℓ A B (a ⊗ₜ[ℤ] f) = a • (homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] := rfl

end ZInQ.Contrib.TateFiniteApproximation
