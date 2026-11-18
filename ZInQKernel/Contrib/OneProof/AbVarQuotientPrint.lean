import ZInQKernel.Contrib.OneProof.AbVarQuotientComplement
import ZInQKernel.Contrib.OneProof.ShimuraQuotientImageSum

/-! Compare the printed quotient with the now-constructed geometric quotient. -/

noncomputable section

namespace ShimuraSteps.Quotient

open CategoryTheory PkgI3 PkgI3.AbVar
open scoped ModularForm

variable {J : AbVar ℚ}

/-- The sum of the saturated annihilator images admits a genuine quotient,
and the printed clause characterizes its map up to isomorphism. -/
theorem exists_genuineQuotient_printQuotient_iff_iso {N : ℕ}
    {ξ : ℕ → AbVar.End J} {f : PkgI4.CF N 2} :
    ∃ (C : AbVar ℚ) (i : AbVar.Hom C J) (Q : AbVar ℚ) (q : AbVar.Hom J Q),
      IsImageSum (Sat (annihilator (printRing ξ f))) i ∧ IsAbVarQuotient i q ∧
        ∀ (A : AbVar ℚ) (ν : AbVar.Hom J A), PrintQuotient ξ f ν ↔
          ∃ a : AbVar.Hom Q A, IsIso a.hom ∧ q.hom ≫ a.hom = ν.hom := by
  obtain ⟨C, i, hi⟩ := imageSum_exists (J := J) (Sat (annihilator (printRing ξ f)))
  obtain ⟨Q, q, hq⟩ := abVarQuotientBySubvarietyExists J C i hi.closed
  exact ⟨C, i, Q, q, hi, hq, fun _ ν => printQuotient_iff_iso ν hi hq⟩

end ShimuraSteps.Quotient
