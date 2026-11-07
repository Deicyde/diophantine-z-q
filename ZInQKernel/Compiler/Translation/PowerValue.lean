import ZInQKernel.Compiler.Translation.TranslateSemantics
import ZInQKernel.Compiler.Translation.PowerScope
import ZInQKernel.Syntax.Recipes.PowerValue

/-!
# Semantics of the power-value recipe

Under M, for all integers `a, b, c` and every `r ∈ ℚ⁵`,
`Rel_power_value(ι(a), ι(b), ι(c), r) ⟺ ∃ w ∈ ℕ^79, r = ι(T(a, b, c, w))`, where `T` is the
polynomial function of the power template (`powerValue_rel_iff`). So `power_value` satisfies (PV)
for the power template (`powerValue_spec`). The value is not required to vanish; nothing is
claimed for non-canonical input codes.

(Blueprint: `compiler/translation/power-value-semantics.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

variable {E : Type}

/-- `T(a, b, c, w₀, …, w₇₈)`: the value of the power template at `(a, b, c, w)`. -/
noncomputable def powerValueT (a b c : ℤ) (w : Fin 79 → ℕ) : ℤ :=
  templateValue powerTemplateCircuit fun i =>
    if i < 3 then [a, b, c].getD i 0 else if h : i - 3 < 79 then (w ⟨i - 3, h⟩ : ℤ) else 0

theorem flatMap_ofFn_getD (L : List (Fin 5 → ℚ)) {i : ℕ} (hi : i < L.length) (m : Fin 5) :
    (L.flatMap List.ofFn).getD (5 * i + m) 0 = L[i] m := by
  induction L generalizing i with
  | nil => simp at hi
  | cons A L ih =>
    rw [List.flatMap_cons]
    rcases i with _ | i
    · rw [List.getD_append _ _ _ _ (by simp)]
      fin_cases m <;> rfl
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_cons_succ]
      rw [show 5 * (i + 1) + ↑m - 5 = 5 * i + m by omega]
      exact ih (by simpa using hi)

theorem paramCode_codeArgs {p : ℕ} (L : List (Fin 5 → ℚ)) (hp : 5 * L.length ≤ p) {i : ℕ}
    (hi : i < L.length) : paramCode (fun k : Fin p => codeArgs L k) i = L[i] := by
  funext m
  simp only [paramCode]
  rw [dite_eq_left (by omega)]
  exact flatMap_ofFn_getD L hi m

theorem powerTemplate_hasCall : ¬ HasCall powerTemplateCircuit :=
  fun ⟨a, b, c, w, h⟩ => powerTemplate_no_call a b c w h

theorem powerConstants_prefix (c3 : ℤ) : powerConstants <+: integerConstants c3 :=
  ⟨[c3, 1399], rfl⟩

theorem powerTemplate_consts :
    ∀ c, NatNode.const c ∈ powerTemplateCircuit.nodes → Nontrivial c → c ∈ powerConstants := by
  intro c hc hn
  have h := powerTemplateCircuit_translationStats.2.2
  have : c ∈ powerTemplateCircuit.nodes.filterMap nontrivialConst :=
    List.mem_filterMap.2 ⟨_, hc, by simp [nontrivialConst, show IsNontrivial c from hn]⟩
  rw [h] at this
  exact this

/-- A circuit without call nodes has the value of its root as a template. -/
theorem circuitValue_eq_templateValue {N : NatCircuit}
    (hN : ∀ a b c w, NatNode.call a b c w ∉ N.nodes) (P : NatCircuit) (θ : ℕ → ℤ) :
    circuitValue P N θ = templateValue N θ := by
  rw [circuitValue, nodeVal, nodeVals, templateValue,
    nodeValues_congr (cv' := fun _ _ _ _ => 0) (θ' := θ) (fun _ _ => rfl)
      fun a b c w h => absurd h (hN a b c w)]

theorem exists_blockAssign_iff {P : NatCircuit} (hP : P.varCount = 82) (a b c : ℤ)
    (Q : ℤ → Prop) :
    (∃ w : Fin (P.varCount - 3) → ℕ, Q (templateValue P (blockAssign P a b c w))) ↔
      ∃ w : Fin 79 → ℕ, Q (templateValue P fun i =>
        if i < 3 then [a, b, c].getD i 0 else if h : i - 3 < 79 then (w ⟨i - 3, h⟩ : ℤ) else 0) := by
  have h79 : P.varCount - 3 = 79 := by omega
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (Fin.cast h79.symm j), ?_⟩
    convert hw using 2
    funext i
    simp only [blockAssign]
    split_ifs with h1 h2 h3 h3 <;> first | rfl | omega
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (Fin.cast h79 j), ?_⟩
    convert hw using 2
    funext i
    simp only [blockAssign]
    split_ifs with h1 h2 h3 h3 <;> first | rfl | omega

section

variable (I : Constructors E) (cstar ell T c3 : ℤ)

/-- **Semantics of the power-value recipe.** Under M, for all `a, b, c ∈ ℤ` and `r ∈ ℚ⁵`,
`Rel_power_value(ι(a), ι(b), ι(c), r) ⟺ ∃ w ∈ ℕ^79, r = ι(T(a, b, c, w))`. -/
theorem powerValue_rel_iff (hI : I.psi = psiComponent) (hM : MultiplicationExact I cstar ell T)
    (recipes : List ExPoly) (a b c : ℤ) (r : Fin 5 → ℚ) :
    ((Recipe.model powerValueRecipe).denote (templateLibrary I cstar ell T c3) recipes).Rel
        (Fin.append (Fin.append (Fin.append (iota a) (iota b)) (iota c)) r) ↔
      ∃ w : Fin 79 → ℕ, r = iota (powerValueT a b c w) := by
  obtain ⟨hwf, -, hin, hvc, hnc, hcore⟩ := powerTemplate_wellFormed
  have hargs : (Fin.append (Fin.append (Fin.append (iota a) (iota b)) (iota c)) r) =
      fun k : Fin 20 => codeArgs [iota a, iota b, iota c, r] k := (codeArgs_four _ _ _ _).symm
  have key := translate_rel_iff_value I cstar ell T c3 (consts := powerConstants)
    (recipes := recipes) hI hM hwf (powerConstants_prefix c3) powerTemplate_consts
    (PowerSetup.none powerTemplate_hasCall) (fun i => [a, b, c].getD i 0) r
    (fun k : Fin 20 => codeArgs [iota a, iota b, iota c, r] k)
    (fun i hi => by
      rw [hin] at hi
      refine (paramCode_codeArgs (p := 20) [iota a, iota b, iota c, r] (by simp) (i := i)
        (by simp; omega)).trans ?_
      interval_cases i <;> rfl)
    (by
      rw [hin]
      exact paramCode_codeArgs (p := 20) (i := 3) [iota a, iota b, iota c, r] (by simp) (by simp))
  rw [hargs]
  refine key.trans ?_
  have hθval : ∀ θ : ℕ → ℤ, circuitValue powerTemplateCircuit powerTemplateCircuit θ =
      templateValue powerTemplateCircuit θ := circuitValue_eq_templateValue hnc _
  have hev := powerTemplate_explicitVars
  constructor
  · rintro ⟨θ, hθ, hc, hr⟩
    refine ⟨fun i => (θ (3 + i)).toNat, ?_⟩
    have hcg : ∀ i < powerTemplateCircuit.varCount, θ i = (if i < 3 then [a, b, c].getD i 0
        else if h : i - 3 < 79 then ((fun i : Fin 79 => (θ (3 + i)).toNat) ⟨i - 3, h⟩ : ℤ) else 0) := by
      intro i hi
      rw [hvc] at hi
      split_ifs with h3 h79
      · exact hc i (by rw [hin]; exact h3)
      · have hmem : (i, VarKind.witness) ∈ powerTemplateCircuit.explicitVars := by
          rw [hev]
          exact List.mem_map.2 ⟨i, List.mem_range.2 hi, by simp [h3]⟩
        have := hθ.1 _ hmem rfl
        simp only at this
        simp only
        rw [show 3 + (i - 3) = i by omega, Int.toNat_of_nonneg this]
      · omega
    rw [hr, hθval, powerValueT]
    exact congrArg iota (templateValue_congr_of_core hcore hcg)
  · rintro ⟨w, hw⟩
    let θ : ℕ → ℤ := fun i =>
      if i < 3 then [a, b, c].getD i 0 else if h : i - 3 < 79 then (w ⟨i - 3, h⟩ : ℤ) else 0
    refine ⟨θ, ⟨fun v hv hk => ?_, fun w' hw' => by rw [powerTemplate_blocks] at hw'; simp at hw'⟩,
      fun i hi => by rw [hin] at hi; simp [θ, hi], ?_⟩
    · rw [hev] at hv
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
      by_cases h3 : i < 3
      · simp [h3] at hk
      · show 0 ≤ θ i
        simp only [θ, h3, ite_false]
        split_ifs <;> simp
    · rw [hw, hθval]
      rfl

/-- `power_value` satisfies (PV) for the power template (as the power recipe of a translation,
read with the template library), under M. -/
theorem powerValue_spec (hI : I.psi = psiComponent) (hM : MultiplicationExact I cstar ell T)
    (recipes : List ExPoly) :
    PowerValueSpec ((Recipe.model powerValueRecipe).denote (templateLibrary I cstar ell T c3) recipes)
      powerTemplateCircuit := by
  intro a b c r
  show ((Recipe.model powerValueRecipe).denote (templateLibrary I cstar ell T c3) recipes).Rel
    (fun k : Fin 20 => codeArgs [iota a, iota b, iota c, r] k) ↔ _
  rw [codeArgs_four, powerValue_rel_iff I cstar ell T c3 hI hM recipes]
  exact (exists_blockAssign_iff powerTemplateCircuit_varCount a b c fun t => r = iota t).symm

end

end ZInQ.Translation
