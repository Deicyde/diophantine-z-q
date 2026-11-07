import ZInQKernel.Compiler.Translation.Completeness

/-!
# Semantics of the model-evaluation translation

Under M (through the callee semantics) and (PV) for the power recipe, the translation `ρ` of a
well-formed natural circuit `𝒩` with `k` inputs means:

1. *zero mode, natural inputs*: `Rel_ρ(E₀, …, E_{k-1})` holds exactly when `E_i = ι(θ_i)` and
   `𝒩(θ) = 0` for some admissible `θ` natural at the inputs (`TranslationShape.rel_iff_zero`); the input
   points need not be assumed to be codes;
2. *value mode, unconstrained inputs*: for integers `c_i`,
   `Rel_ρ(ι(c₀), …, ι(c_{k-1}), r)` holds exactly when `r = ι(𝒩(θ))` for some admissible `θ`
   with `θ_i = c_i` (`TranslationShape.rel_iff_value`); nothing is claimed for non-canonical inputs.

The parameters `a` of `ρ` are read as the codes `paramCode a i = (a_{5i}, …, a_{5i+4})`.

(Blueprint: `compiler/translation/model-evaluation-semantics.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

/-- The code `(a_{5i}, …, a_{5i+4})` of the parameter point `i` (zero beyond the parameters). -/
def paramCode {p : ℕ} (a : Fin p → ℚ) (i : ℕ) : Fin 5 → ℚ :=
  fun m => if h : 5 * i + m < p then a ⟨5 * i + m, h⟩ else 0

theorem refVal_param {g : Fin 3 → ℕ} {x : ℕ → ℚ} {p : ℕ} {a : Fin p → ℚ}
    (hx : ∀ i (hi : i < p), x i = a ⟨i, hi⟩) {i : ℕ} (hi : 5 * i + 5 ≤ p) :
    refVal g x (5 * i : ℕ) = paramCode a i := by
  rw [refVal_natCast]
  funext m
  simp only [pointAt, paramCode]
  rw [dite_eq_left (by omega)]
  exact hx _ _

/-- An assignment whose parameter points are the given codes extends the parameters. -/
theorem extends_params {x : ℕ → ℚ} {p k : ℕ} (hp : p = 5 * k) {a : Fin p → ℚ}
    {g : Fin 3 → ℕ} (h : ∀ i < k, refVal g x (5 * i : ℕ) = paramCode a i) :
    ∀ i (hi : i < p), x i = a ⟨i, hi⟩ := by
  intro i hi
  have hk : i / 5 < k := by omega
  have h1 := congrFun (h (i / 5) hk) ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩
  rw [refVal_natCast] at h1
  simp only [pointAt, paramCode] at h1
  rw [dite_eq_left (by omega)] at h1
  have he : 5 * (i / 5) + i % 5 = i := Nat.div_add_mod i 5
  simp only [he] at h1
  exact h1

section

variable {templates recipes : List ExPoly} {scalarOf : ℤ → ExPoly} {r : ModelRecipe}
  {P N : NatCircuit} {V : ℕ}

/-- **Semantics of the model-evaluation translation, zero mode with natural inputs.** -/
theorem TranslationShape.rel_iff_zero (S : TranslationShape templates recipes scalarOf r P N false true)
    (hwf : WellFormed P N V) (hsem : CalleeSemantics (getEx templates r.natural)
      (getEx templates r.addition) (getEx templates r.multiplication) scalarOf)
    (hπ : HasCall N → PowerValueSpec (powerCallee recipes r) P)
    (hsc : ScopedIn (r.formula templates recipes) r.parameterCount r.variableCount)
    (a : Fin r.parameterCount → ℚ) :
    ((Recipe.model r).denote templates recipes).Rel a ↔
      ∃ θ : ℕ → ℤ, Admissible P N θ ∧
        (∀ i < N.inputCount, 0 ≤ θ i ∧ paramCode a i = iota (θ i)) ∧ circuitValue P N θ = 0 := by
  have hp : r.parameterCount = 5 * N.inputCount := by simpa using S.params
  rw [modelRecipe_rel_iff templates recipes r hsc]
  constructor
  · rintro ⟨x, hxa, hx⟩
    obtain ⟨θ, hθ, hin, -, hnode⟩ :=
      translate_sound S hwf hsem hπ hx.toModelHoldsExceptRoot (fun h => absurd h (by simp))
    refine ⟨θ, hθ, fun i hi => ⟨(hin i hi).2 rfl, ?_⟩, ?_⟩
    · rw [← refVal_param hxa (by omega)]
      exact_mod_cast (hin i hi).1
    · have hroot := hx.root
      rw [S.root] at hroot
      simp only [Bool.false_eq_true, ite_false] at hroot
      rw [hnode _ hwf.core.root_lt, (refVal_negative hx.toModelHoldsExceptRoot).1] at hroot
      exact iota_injective hroot
  · rintro ⟨θ, hθ, hin, h0⟩
    obtain ⟨hinput, -, -, -, hall⟩ :=
      translate_complete S hwf hsem hπ hθ fun _ i hi => (hin i hi).1
    refine ⟨S.witness θ, extends_params (g := r.generator) hp fun i hi => ?_, hall (Or.inr h0)⟩
    rw [(hin i hi).2]
    exact_mod_cast hinput i hi

/-- **Semantics of the model-evaluation translation, value mode with unconstrained inputs.** -/
theorem TranslationShape.rel_iff_value (S : TranslationShape templates recipes scalarOf r P N true false)
    (hwf : WellFormed P N V) (hsem : CalleeSemantics (getEx templates r.natural)
      (getEx templates r.addition) (getEx templates r.multiplication) scalarOf)
    (hπ : HasCall N → PowerValueSpec (powerCallee recipes r) P)
    (hsc : ScopedIn (r.formula templates recipes) r.parameterCount r.variableCount)
    (c : ℕ → ℤ) (R : Fin 5 → ℚ) (a : Fin r.parameterCount → ℚ)
    (ha : ∀ i < N.inputCount, paramCode a i = iota (c i)) (hR : paramCode a N.inputCount = R) :
    ((Recipe.model r).denote templates recipes).Rel a ↔
      ∃ θ : ℕ → ℤ, Admissible P N θ ∧ (∀ i < N.inputCount, θ i = c i) ∧
        R = iota (circuitValue P N θ) := by
  have hp : r.parameterCount = 5 * (N.inputCount + 1) := by simpa using S.params
  rw [modelRecipe_rel_iff templates recipes r hsc]
  constructor
  · rintro ⟨x, hxa, hx⟩
    have hpar : ∀ i < N.inputCount, refVal r.generator x (5 * i : ℕ) = iota (c i) :=
      fun i hi => by rw [refVal_param hxa (by omega), ha i hi]
    obtain ⟨θ, hθ, hin, -, hnode⟩ := translate_sound S hwf hsem hπ hx.toModelHoldsExceptRoot
      fun _ i hi => ⟨c i, by exact_mod_cast hpar i hi⟩
    refine ⟨θ, hθ, fun i hi => iota_injective ?_, ?_⟩
    · rw [← (hin i hi).1]
      exact_mod_cast hpar i hi
    · have hroot := hx.root
      rw [S.root] at hroot
      simp only [ite_true] at hroot
      rw [hnode _ hwf.core.root_lt] at hroot
      rw [← hR, ← refVal_param hxa (by omega)]
      exact_mod_cast hroot.symm
  · rintro ⟨θ, hθ, hin, hRv⟩
    obtain ⟨hinput, hout, -, -, hall⟩ :=
      translate_complete S hwf hsem hπ hθ fun h => absurd h (by simp)
    refine ⟨S.witness θ, extends_params (g := r.generator) hp fun i hi => ?_, hall (Or.inl rfl)⟩
    rcases Nat.lt_or_ge i N.inputCount with hi' | hi'
    · rw [ha i hi', ← hin i hi']
      exact_mod_cast hinput i hi'
    · obtain rfl : i = N.inputCount := by omega
      rw [hR, hRv]
      exact_mod_cast hout rfl

end

end ZInQ.Translation
