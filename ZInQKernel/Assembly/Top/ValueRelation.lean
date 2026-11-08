import ZInQKernel.Assembly.Top.Spec
import ZInQKernel.Assembly.Top.MainBranch
import ZInQKernel.Assembly.Local.TestCompleteness
import ZInQKernel.Assembly.Close
import ZInQKernel.Multiplication.Top

/-!
# The exact ordinary-value relation

Blueprint: `assembly/main-branch-exactness.md` and `assembly/ordinary-value-relation.md`.

`Rel_value(N, t)` holds exactly when `N` is accepted by membership and either the exceptional
relation holds or some `K` satisfies both `Rel_close(N, K, t)` and `Rel_{value.test}(N, K, t)`
(the outer recipe relations). Membership gives `N = ι(n)`; the exceptional branch gives `t = n`
outright, and in the main branch soundness of Close and the six local tests force `t = n`
(`main_branch_eq_of`). Conversely, for `n ∉ 𝒞` one suitable shift `κ` satisfies the tests
(`test_complete`) and Close holds for that same shift (completeness of Close).

The theorems with suffix `_of` take soundness and completeness of Close as hypotheses; the final
theorems instantiate them with `close_sound` and `close_complete` (`Assembly/Close/`) and input M
with `Mult.multiplication_exact`, all three under the hypotheses H, PC and the slope
representation SR (`Mult.SlopeRepresentation`, a consequence of 22P and of 22P₂).
-/

namespace ZInQ.Assembly

open Syntax Compiler.Precision Compiler.Universal

/-- **An accepting main branch forces the exact value**, from soundness of Close: if
`Rel_close(ι(n), ι(κ), t)` and `Test(n, κ, t)`, then `t = n`. -/
theorem main_branch_eq_of (hH : SixContactMin)
    (hsound : ∀ (n κ : ℤ) (t : ℚ), CloseRel (iota n) (iota κ) t →
      (n : ℚ) ∉ contactSet ∧ κ ≠ 0 ∧ |(t : ℝ) - n| < Real.exp (-(bound n κ : ℝ)))
    {n κ : ℤ} {t : ℚ} (hc : CloseRel (iota n) (iota κ) t) (hT : Test n κ t) : t = n := by
  obtain ⟨hn, -, hclose⟩ := hsound n κ t hc
  exact eq_of_close_of_test hH ((cast_mem_contactSet_iff n).not.1 hn) hclose hT

/-- **The exact ordinary-value relation**, from soundness and completeness of Close:
`Rel_value(N, t) ⟺ ∃ n ∈ ℤ, N = ι(n) ∧ t = n`. -/
theorem value_relation_iff_of (hH : SixContactMin) (hPC : PoleCompleteness)
    (hM : SpecMultiplicationExact)
    (hsound : ∀ (n κ : ℤ) (t : ℚ), CloseRel (iota n) (iota κ) t →
      (n : ℚ) ∉ contactSet ∧ κ ≠ 0 ∧ |(t : ℝ) - n| < Real.exp (-(bound n κ : ℝ)))
    (hcomp : ∀ n κ : ℤ, (n : ℚ) ∉ contactSet → κ ≠ 0 → CloseRel (iota n) (iota κ) n)
    (N : Fin 5 → ℚ) (t : ℚ) :
    ValueRel N t ↔ ∃ n : ℤ, N = iota n ∧ t = n := by
  unfold ValueRel closeSpecLib
  rw [spec_value_rel_iff, spec_valueUnion_rel_iff, spec_main_rel_iff,
    rel_member_iff_existsUnique_iota, exceptions_rel_iff]
  simp only [valueTest_rel_iff hM]
  constructor
  · rintro ⟨-, ⟨c, -, hc, htc⟩ | ⟨K, hcl, n, κ, rfl, rfl, hT⟩⟩
    · exact ⟨c, hc, htc⟩
    · exact ⟨n, rfl, main_branch_eq_of hH hsound hcl hT⟩
  · rintro ⟨n, rfl, rfl⟩
    refine ⟨⟨n, rfl, fun m hm => (iota_injective hm).symm⟩, ?_⟩
    by_cases hn : n ∈ contacts
    · exact Or.inl ⟨n, hn, rfl, rfl⟩
    · have hn' := (cast_mem_contactSet_iff n).not.2 hn
      obtain ⟨κ, hκ, hT⟩ := test_complete hPC n hn'
      exact Or.inr ⟨iota κ, hcomp n κ hn' hκ, n, κ, rfl, rfl, hT⟩

/-- **Projection of the exact ordinary-value relation**, from soundness and completeness of
Close: `(∃ N ∈ ℚ⁵, Rel_value(N, t)) ⟺ t ∈ ℤ`. -/
theorem exists_value_relation_iff_of (hH : SixContactMin) (hPC : PoleCompleteness)
    (hM : SpecMultiplicationExact)
    (hsound : ∀ (n κ : ℤ) (t : ℚ), CloseRel (iota n) (iota κ) t →
      (n : ℚ) ∉ contactSet ∧ κ ≠ 0 ∧ |(t : ℝ) - n| < Real.exp (-(bound n κ : ℝ)))
    (hcomp : ∀ n κ : ℤ, (n : ℚ) ∉ contactSet → κ ≠ 0 → CloseRel (iota n) (iota κ) n) (t : ℚ) :
    (∃ N : Fin 5 → ℚ, ValueRel N t) ↔ ∃ z : ℤ, (z : ℚ) = t := by
  simp only [value_relation_iff_of hH hPC hM hsound hcomp]
  constructor
  · rintro ⟨N, n, -, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨iota z, z, rfl, rfl⟩

/-- **An accepting main branch forces the exact value.** Under H, PC and SR, if
`Rel_close(ι(n), ι(κ), t)` and `Test(n, κ, t)`, then `t = n`. -/
theorem main_branch_eq (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : Mult.SlopeRepresentation) {n κ : ℤ} {t : ℚ} (hc : CloseRel (iota n) (iota κ) t)
    (hT : Test n κ t) : t = n :=
  main_branch_eq_of hH (close_sound (Mult.multiplication_exact hH hPC h22)) hc hT

/-- **The exact ordinary-value relation.** Under H, PC and SR, for all `N ∈ ℚ⁵` and `t ∈ ℚ`,
`Rel_value(N, t) ⟺ ∃ n ∈ ℤ, N = ι(n) ∧ t = n`. -/
theorem value_relation_iff (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : Mult.SlopeRepresentation) (N : Fin 5 → ℚ) (t : ℚ) :
    ValueRel N t ↔ ∃ n : ℤ, N = iota n ∧ t = n :=
  have hM := Mult.multiplication_exact hH hPC h22
  value_relation_iff_of hH hPC hM (close_sound hM) (close_complete hM) N t

/-- **The exact ordinary-value relation, projected.** Under H, PC and SR, for every `t ∈ ℚ`,
`(∃ N ∈ ℚ⁵, Rel_value(N, t)) ⟺ t ∈ ℤ`. -/
theorem exists_value_relation_iff (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : Mult.SlopeRepresentation) (t : ℚ) :
    (∃ N : Fin 5 → ℚ, ValueRel N t) ↔ ∃ z : ℤ, (z : ℚ) = t :=
  have hM := Mult.multiplication_exact hH hPC h22
  exists_value_relation_iff_of hH hPC hM (close_sound hM) (close_complete hM) t

end ZInQ.Assembly
