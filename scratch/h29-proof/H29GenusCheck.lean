import ZInQKernel.Contrib.OneProof.TYZLemma29Genus

/-! h29-proof checks: the target statement copied verbatim from
`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean:455` (checked equal by `rfl`), the main theorem, axioms. -/

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus ZInQ.RouteK.Rank5b
open scoped Quaternion

/-- `hL29`, verbatim. -/
def TYZLemma29PrintedNe3Copy : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → n ≠ 3 → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℤ, IsLcalSign ℓ →
        ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧
          ∑ d ∈ pairIdx n, ε d * (ℓ (n / d) * ℓ d) = genusPeriodTV n τ f

example : TYZLemma29PrintedNe3Copy = TYZLemma29PrintedNe3 := rfl

theorem hL29_of_genus (h21 : TYZThm21Pairs) (h28 : TYZLemma28Sym) : TYZLemma29PrintedNe3Copy :=
  tyzLemma29PrintedNe3_of_genus h21 h28

#print axioms hL29_of_genus
#print axioms tyzLemma29Printed_of_genus
#print axioms tyzThm21At31_of_thm21Pairs
#print axioms tyzLemma29Mod2_of_genusLeaves
#print axioms torsionOrder_qNeg_eq_two
