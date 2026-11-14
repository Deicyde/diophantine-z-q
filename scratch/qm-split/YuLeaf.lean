import TailK

/-!
# qm-split, row H-35: `PkgI3.QMDichotomyYu` from Yu's Theorem 1.1 in published form

The row (`HDec.PkgI3.QMDichotomyYu`, leaf-fold4 chain `LPrefix.lean` l.2892, imported) is Yu's theorem
with the splitting clause dropped. The leaf below keeps the clause: in the second case the imaginary
quadratic field `k = ℚ(√d)` splits `B`, `k ⊗_ℚ B ≅ M₂(k)`. The proof of the row drops it.

Check: `scratch/qm-split/chk.sh scratch/qm-split/YuLeaf.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Yu

open HDec HDec.PkgI3 PkgI3.AbVar Polynomial
open scoped Quaternion TensorProduct

/-- **LEAF (Chia-Fu Yu, *Endomorphism algebras of QM abelian surfaces*, J. Pure Appl. Algebra 217 (2013),
Thm 1.1, journal p. 907; arXiv:1210.1125 Thm 1.1; the journal first page was read by the locator audit,
`docs/research/locators.md` row T27; volume number UNVERIFIED).** Let `A` be an abelian surface over an
algebraically closed field `k` of characteristic `0`, and `B = (a, b)_ℚ` an indefinite quaternion division
algebra with a `ℚ`-algebra embedding `B → End⁰(A)`. Then `End⁰(A) ≅ B`, or `End⁰(A) ≅ M₂(K)` for an
imaginary quadratic field `K = ℚ(√d)`, `d < 0`, that splits `B` (`K ⊗_ℚ B ≅ M₂(K)` as `K`-algebras).

Form: the printed statement in characteristic `0`, except that the attribution of the two cases (simple
`A` in the first, non-simple `A` in the second, as the audit reads the theorem) is dropped (a weaker
conclusion). `End⁰(A) = ℚ ⊗_ℤ End(A)` (`PkgI3.AbVar.End0`) over the kernel's abelian varieties
`PkgI3.AbVar`; the division hypothesis is "every nonzero element is a unit"; indefinite is
`QuatIndefinite a b` (`0 < a ∨ 0 < b`), the same hypotheses as the row. -/
def YuThm11 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, QuatIndefinite a b → (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) ∧
            Nonempty ((AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) ⊗[ℚ] ℍ[ℚ, a, b] ≃ₐ[AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)]
              Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- **Row H-35 from the published form**: drop the splitting clause. -/
theorem qmDichotomyYu_of_yu (h : YuThm11) : PkgI3.QMDichotomyYu := by
  intro k _ _ _ A hA a b hind hdiv hemb
  rcases h k A hA a b hind hdiv hemb with h1 | ⟨d, hd, h2, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨d, hd, h2⟩

end HDec.QMSplit.Yu

#print axioms HDec.QMSplit.Yu.qmDichotomyYu_of_yu

example : HDec.QMSplit.Yu.YuThm11 → HDec.PkgI3.QMDichotomyYu := HDec.QMSplit.Yu.qmDichotomyYu_of_yu
