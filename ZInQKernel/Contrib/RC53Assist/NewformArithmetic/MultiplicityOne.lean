import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Across

namespace ZInQ.Contrib.RC53Assist.NewformArithmetic

open UpperHalfPlane HeckeRing.GL2

/-- Li's weight-two, trivial-character specialization, on the genuine newform
objects. The vendored theorem compares the induced characters at the common
level and the normalized Hecke eigenvalues away from both levels. -/
theorem multiplicity_one_weight_two
    (M N : ℕ) [NeZero M] [NeZero N] (F : Newform M 2) (G : Newform N 2)
    (hF : F.χ = 1) (hG : G.χ = 1)
    (h : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (qExpansion 1 G.toCuspForm).coeff p) :
    M = N ∧ ∀ τ : UpperHalfPlane, F.toCuspForm τ = G.toCuspForm τ := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨hMN, hfun⟩ := Newform.level_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq
    F G (S := S) (by rw [hF, hG, MonoidHom.one_comp, MonoidHom.one_comp])
    (fun p hp hpM hpN hpS => by
      rw [← F.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue F.isNorm ⟨p, hp.pos⟩ hpM,
        ← G.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue G.isNorm ⟨p, hp.pos⟩ hpN]
      exact hS p hp hpS)
  exact ⟨hMN, congrFun hfun⟩

end ZInQ.Contrib.RC53Assist.NewformArithmetic
