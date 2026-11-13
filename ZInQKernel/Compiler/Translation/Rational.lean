import ZInQKernel.Compiler.Translation.PowerValue
import ZInQKernel.Compiler.Translation.PrecisionScope
import ZInQKernel.Syntax.Recipes.Precision

/-!
# Semantics of the rational translation

Under M, for all rational `5`-tuples `E₀, …, E₄` (not assumed to be codes),
`Rel_precision(E₀, …, E₄)` holds exactly when `E_i = ι(c_i)` for natural numbers `c_i` at which the
natural precision polynomial `C = [[𝒩]]` has a natural zero: `C(c, z) = 0` for some
`z ∈ ℕ^1305806` (`precision_rel_iff`). This is input C on the rational side; with equation (C.4)
the precision recipe holds at `ι(c₀), …, ι(c₄)` exactly when the precision relation accepts `c`
(`precision_rel_iff_accepts_of`).

The precision recipe calls the power-value recipe as recipe `0` of the recipe library; the
statement takes a recipe library whose recipe `0` is `power_value` (denoted over any earlier
recipes).

(Blueprint: `compiler/translation/rational-translation.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Compiler.Universal Syntax

variable {E : Type}

/-- The call template of the power template is the power template. -/
theorem callTemplate_powerTemplate : callTemplate powerTemplateCircuit = powerTemplate := by
  have h : callTemplate powerTemplateCircuit =
      ⟨3, powerTemplateCircuit.varCount - 3, powerTemplateCircuit.poly ExPoly.empty⟩ := rfl
  rw [h, powerTemplateCircuit_varCount]
  show (⟨3, 79, powerTemplateCircuit.poly ExPoly.empty⟩ : ExPoly) = ⟨3, 79, powerTemplate.poly⟩
  rw [powerTemplate_poly_def]
  rfl

/-- The value of the precision circuit is the natural precision polynomial `[[𝒩]]`. -/
theorem circuitValue_precision (θ : ℕ → ℤ) :
    circuitValue powerTemplateCircuit precisionCircuit θ =
      MvPolynomial.eval θ (precisionCircuit.poly powerTemplate) := by
  rw [circuitValue_eq_eval_poly, circuitPoly, callTemplate_powerTemplate]

/-- The translated recipes are well formed (as existential polynomials) under their witness
scope. -/
theorem denote_wf_of_scopedIn {templates recipes : List ExPoly} {r : ModelRecipe}
    (h : ScopedIn (r.formula templates recipes) r.parameterCount r.variableCount) :
    ((Recipe.model r).denote templates recipes).WF := by
  have e : Recipe.poly templates recipes (.model r) = (r.formula templates recipes).compile :=
    Recipe.poly_eq_compile templates recipes (.model r)
  show VarsLT (Recipe.poly templates recipes (.model r))
    (r.parameterCount + (r.variableCount - r.parameterCount))
  rw [e, Nat.add_sub_cancel' h.le]
  exact h.varsLT

theorem paramCode_rows (E : Fin 5 → Fin 5 → ℚ) {i : ℕ} (hi : i < 5) :
    paramCode (p := 25) (fun k => E ⟨k / 5, by omega⟩ ⟨k % 5, by omega⟩) i = E ⟨i, hi⟩ := by
  funext m
  simp only [paramCode]
  rw [dite_eq_left (by omega)]
  refine congrArg₂ E (Fin.ext ?_) (Fin.ext ?_) <;> simp; omega

section

variable (I : Constructors E) (cstar ell T : ℤ)

/-- The power setup of the precision recipe: recipe `0` is `power_value`. -/
theorem precision_powerSetup (hI : I.psi = psiComponent) (hM : MultiplicationExact I cstar ell T)
    {recipes : List ExPoly} (hrec : ∃ rs, getEx recipes 0 =
      (Recipe.model powerValueRecipe).denote (templateLibrary I cstar ell T c3) rs) :
    PowerSetup recipes
      (some (0, powerValueRecipe.variableCount - powerValueRecipe.parameterCount))
      powerTemplateCircuit precisionCircuit := by
  obtain ⟨rs, hrs⟩ := hrec
  have hsc := translate_scopedIn_library I cstar ell T c3 (recipes := rs) (mode := .value)
    (natIn := false) powerTemplate_wellFormed.1 (powerConstants_prefix c3) powerTemplate_consts
    (PowerSetup.none powerTemplate_hasCall)
  refine ⟨fun i w h => ?_, fun i w h => ?_, fun _ => rfl, fun i w h _ => ?_⟩
  · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hrs]
    exact denote_wf_of_scopedIn hsc
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hrs]
    simp only [Recipe.denote, Recipe.variableCount, Recipe.parameterCount]
  · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hrs]
    exact powerValue_spec I cstar ell T c3 hI hM rs

/-- **Semantics of the rational translation.** Under M, for all `E₀, …, E₄ ∈ ℚ⁵`,
`Rel_precision(E₀, …, E₄)` holds exactly when `E_i = ι(c_i)` for some `c ∈ ℕ⁵` and
`C(c, z) = 0` for some `z ∈ ℕ^1305806`, where `C` is the natural precision polynomial. -/
theorem precision_rel_iff (hI : I.psi = psiComponent) (hM : MultiplicationExact I cstar ell T)
    (recipes : List ExPoly) (hrec : ∃ rs, getEx recipes 0 =
      (Recipe.model powerValueRecipe).denote (templateLibrary I cstar ell T c3) rs)
    (E : Fin 5 → Fin 5 → ℚ) :
    ((Recipe.model (precisionRecipe precisionCircuit c3)).denote
        (templateLibrary I cstar ell T c3) recipes).Rel
        (fun k : Fin 25 => E ⟨k / 5, by omega⟩ ⟨k % 5, by omega⟩) ↔
      ∃ c : Fin 5 → ℕ, (∀ i, E i = iota (c i)) ∧ ∃ z : Fin 1305806 → ℕ,
        MvPolynomial.eval (fun i => (NatCircuit.natPoint 5 1305806 c z i : ℤ))
          (precisionCircuit.poly powerTemplate) = 0 := by
  obtain ⟨hwf, -, -, -⟩ := precisionCircuit_wellFormed
  have hws := precisionCircuit_wellScoped
  have hV : precisionCircuit.varCount = 1305811 := precisionCircuit_counts.2.2.2.1
  have hk : precisionCircuit.inputCount = 5 := rfl
  have hcmem : ∀ c, NatNode.const c ∈ precisionCircuit.nodes → Nontrivial c →
      c ∈ integerConstants c3 := fun c hc hn => by
    have := precisionCircuitOf_consts c3 hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    obtain ⟨h0, h1, h2⟩ := hn
    simp only [integerConstants, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have key := translate_rel_iff_zero I cstar ell T c3 hI hM hwf (List.prefix_refl _) hcmem
    (precision_powerSetup I cstar ell T hI hM hrec)
    (fun k : Fin 25 => E ⟨k / 5, by omega⟩ ⟨k % 5, by omega⟩)
  refine key.trans ?_
  simp only [hk, circuitValue_precision]
  constructor
  · rintro ⟨θ, hθ, hin, h0⟩
    refine ⟨fun i => (θ i).toNat, fun i => ?_, fun j => (θ (5 + j)).toNat, ?_⟩
    · have this : paramCode (p := 25) (fun k => E ⟨k / 5, by omega⟩ ⟨k % 5, by omega⟩) i =
          iota (θ i) := (hin i i.isLt).2
      rw [paramCode_rows E i.isLt] at this
      rw [this, Int.toNat_of_nonneg (hin i i.isLt).1]
    · rw [← h0]
      rw [← circuitValue_precision, ← circuitValue_precision]
      refine circuitValue_congr_lt hwf fun i hi => ?_
      have hnn : 0 ≤ θ i := by
        rcases Nat.lt_or_ge i 5 with h5 | h5
        · exact (hin i h5).1
        · rcases hws.cover i (by rw [hV]; exact hi) with ⟨v, hv, rfl⟩ | ⟨w, hw, hiw⟩
          · cases hk' : v.2
            · exact absurd (lt_of_input hwf.core hv hk') (by rw [hk]; omega)
            · exact hθ.1 v hv hk'
          · simp only [NatCircuit.InBlock, powerWitnesses] at hiw
            have := hθ.2 w hw (i - w) (by rw [powerTemplateCircuit_varCount]; omega)
            rwa [show w + (i - w) = i by omega] at this
      simp only [NatCircuit.natPoint]
      split_ifs with h5 h6
      · simp [Int.toNat_of_nonneg hnn]
      · simp only [Int.toNat_of_nonneg (show 0 ≤ θ (5 + (i - 5)) by
          rw [show 5 + (i - 5) = i by omega]; exact hnn)]
        rw [show 5 + (i - 5) = i by omega]
      · omega
  · rintro ⟨c, hc, z, hz⟩
    refine ⟨fun i => (NatCircuit.natPoint 5 1305806 c z i : ℤ),
      ⟨fun _ _ _ => Int.natCast_nonneg _, fun _ _ _ _ => Int.natCast_nonneg _⟩,
      fun i hi => ⟨Int.natCast_nonneg _, ?_⟩, hz⟩
    show paramCode (p := 25) (fun k => E ⟨k / 5, by omega⟩ ⟨k % 5, by omega⟩) i = _
    rw [paramCode_rows E hi, hc ⟨i, hi⟩]
    simp [NatCircuit.natPoint, hi]

/-- With equation (C.4), the precision recipe holds at `E₀, …, E₄` exactly when `E_i = ι(c_i)`
for some `c ∈ ℕ⁵` accepted by the precision relation. -/
theorem precision_rel_iff_accepts_of (hI : I.psi = psiComponent)
    (hM : MultiplicationExact I cstar ell T)
    (hC4 : ∀ c : Fin 5 → ℕ, (∃ z : Fin 1305806 → ℕ,
      MvPolynomial.eval (fun i => (NatCircuit.natPoint 5 1305806 c z i : ℤ))
        (precisionCircuit.poly powerTemplate) = 0) ↔ Compiler.Precision.accepts c)
    (recipes : List ExPoly) (hrec : ∃ rs, getEx recipes 0 =
      (Recipe.model powerValueRecipe).denote (templateLibrary I cstar ell T c3) rs)
    (E : Fin 5 → Fin 5 → ℚ) :
    ((Recipe.model (precisionRecipe precisionCircuit c3)).denote
        (templateLibrary I cstar ell T c3) recipes).Rel
        (fun k : Fin 25 => E ⟨k / 5, by omega⟩ ⟨k % 5, by omega⟩) ↔
      ∃ c : Fin 5 → ℕ, (∀ i, E i = iota (c i)) ∧ Compiler.Precision.accepts c := by
  rw [precision_rel_iff I cstar ell T hI hM recipes hrec]
  exact exists_congr fun c => and_congr_right fun _ => hC4 c

end

end ZInQ.Translation
