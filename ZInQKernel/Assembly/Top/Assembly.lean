import ZInQKernel.Assembly.Top.ValueRelation
import ZInQKernel.Size.Majorants.Bound
import ZInQKernel.Target

/-!
# The assembly lemma

Blueprint: `assembly/assembly-lemma.md`.

The specified polynomial is `P_* = specPstar c₃` at the program literal `c₃ = code(𝒲)`. Its
rational zero projection is the projection of `Rel_value` (`specPstar_zero_projection`), which is
`ℤ` by the exact ordinary-value relation; its degree and coefficients are bounded by the size
chapter under the catalogue bound (`Pstar_target_bounds`, with `|c₃| < 2^(2^24)` from `c3_lt'`).
Both the zero projection and the size bounds use the shape of the natural precision circuit,
hence the node statistics of the universal halting circuit, the named finite check
`HaltingNodeCheck`.
-/

namespace ZInQ.Assembly

open Syntax Compiler.Universal

/-- `|c₃| < 2^(2^24)`, the size of the program literal used by the size chapter. -/
theorem c3_natAbs_lt : ((c3 : ℤ)).natAbs < 2 ^ 2 ^ 24 := by
  rw [Int.natAbs_natCast]
  exact c3_lt'

/-- The rational zero projection of `P_*` is the projection of `Rel_value`. -/
theorem specPstar_zero_projection_valueRel (hN : HaltingNodeCheck) (q : ℚ) :
    (∃ w : Fin 292890231904 → ℚ,
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (specPstar (c3 : ℤ)) = 0) ↔
      ∃ N : Fin 5 → ℚ, ValueRel N q := by
  rw [specPstar_zero_projection _ hN]
  refine exists_congr fun N => ?_
  rw [ValueRel, show [q] = List.ofFn ![q] from rfl, ← List.ofFn_fin_append]
  exact (valRel_ofFn_iff _ (valueExPoly_params _ _ _ _ _ _) _).symm

/-- **The assembly lemma**, from the projection of the exact ordinary-value relation: `P_*` has
degree below `2↑↑7`, coefficients below `2↑↑8` and rational zero projection `ℤ`. -/
theorem Pstar_spec_of (hN : HaltingNodeCheck) (hCAT : CatalogueBound)
    (hval : ∀ t : ℚ, (∃ N : Fin 5 → ℚ, ValueRel N t) ↔ ∃ z : ℤ, (z : ℚ) = t) :
    (specPstar (c3 : ℤ)).totalDegree < hyperoperation 4 2 7 ∧
      (∀ m : Fin 292890231905 →₀ ℕ, ((specPstar (c3 : ℤ)).coeff m).natAbs <
        hyperoperation 4 2 8) ∧
      ∀ q : ℚ, (∃ w : Fin 292890231904 → ℚ,
          MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (specPstar (c3 : ℤ)) = 0) ↔
        ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨hdeg, hcoeff⟩ := Size.Pstar_target_bounds hCAT hN c3_natAbs_lt
  exact ⟨hdeg, hcoeff, fun q => (specPstar_zero_projection_valueRel hN q).trans (hval q)⟩

/-- **The assembly lemma** (target form), from M and soundness and completeness of Close. -/
theorem assembly_of (hN : HaltingNodeCheck) (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (hCAT : CatalogueBound) (hM : SpecMultiplicationExact)
    (hsound : ∀ (n κ : ℤ) (t : ℚ), CloseRel (iota n) (iota κ) t →
      n ∉ Compiler.Precision.contacts ∧ κ ≠ 0 ∧
        |(t : ℝ) - n| < Real.exp (-(Compiler.Precision.bound n κ : ℝ)))
    (hcomp : ∀ n κ : ℤ, n ∉ Compiler.Precision.contacts → κ ≠ 0 → CloseRel (iota n) (iota κ) n) :
    FrozenTarget :=
  ⟨specPstar (c3 : ℤ), Pstar_spec_of hN hCAT (exists_value_rel_iff_of hH hPC hM hsound hcomp)⟩

end ZInQ.Assembly
