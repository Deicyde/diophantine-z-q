import ZInQKernel.Size.Majorants.Rules
import ZInQKernel.Size.Majorants.Height

/-!
# Recipes satisfy the height majorant

Blueprint: `size/majorants/recipe-majorant.md`.

Let `B ≥ 2^20`.

1. A model-evaluation recipe with at most `B` conjuncts whose callees satisfy the majorant at
   their heights satisfies the majorant at `max(4, max_κ (H(κ) + 3)) + 2`
   (`model_majorant`). The point references are variables, `0`, `1`, `-145` or negated
   variables, so the arguments of every call and the generator equations and root
   differences have height at most one.
2. A composition recipe with at most `B` calls satisfies the majorant at `max_i H(κ_i) + 2`
   (sum of squares) or `max_i H(κ_i) + 1` (product) (`composition_majorant`): the arguments of
   its calls are variables, so every call keeps the height of its callee
   (`Maj.bind₁_of_maj_zero`).

Both are stated with the recipe heights of `ZInQKernel.Size.Majorants.Height`.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {B : ℕ}

theorem Scale.maj_one {σ : Type*} {s : ℕ} {P : MvPolynomial σ ℤ} (hP : Scale B 0 s P)
    (hs : 2 ^ s ≤ B ^ 8) : Maj B 1 P :=
  Scale.maj_succ (h := 0) (by simpa using hP) hs

/-- Every entry of a point reference has degree at most `1` and norm at most `145`. -/
theorem sz_pointRef (hB : 1 ≤ B) (g : Fin 3 → ℕ) (r : ℤ) (i : Fin 5) :
    Scale B 0 3 (pointRef g r i) := by
  have h145 : Scale B 0 3 (-145 : Poly) := (Scale.ofNat hB 145 (by norm_num)).neg
  rcases r with r | n
  · exact Scale.X hB _
  · rcases n with _ | _ | _ | n
    · fin_cases i
      · exact Scale.one hB
      all_goals exact Scale.zero hB
    · fin_cases i
      · exact Scale.zero hB
      · exact Scale.X hB _
      · exact h145
      · exact Scale.X hB _
      · exact Scale.X hB _
    · fin_cases i
      · exact Scale.zero hB
      · exact Scale.X hB _
      · exact h145
      · exact (Scale.X hB _).neg
      · exact (Scale.X hB _).neg
    · exact Scale.zero hB

theorem maj_pointRef (hB : 2 ^ 20 ≤ B) (g : Fin 3 → ℕ) (r : ℤ) (i : Fin 5) :
    Maj B 1 (pointRef g r i) :=
  (sz_pointRef (one_le_of_two_pow_twenty_le hB) g r i).maj_one
    (two_pow_le_pow_eight hB (by norm_num))

theorem maj_mem_pointRefList (hB : 2 ^ 20 ≤ B) (g : Fin 3 → ℕ) (r : ℤ) :
    ∀ f ∈ pointRefList g r, Maj B 1 f := by
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
  exact maj_pointRef hB g r i

/-- A call on a list of argument polynomials of height at most `k` (missing arguments read as
`0`) has height at most `H + k + 1`. -/
theorem Maj.callList {H k : ℕ} (hB : 2 ^ 20 ≤ B) {τ : ExPoly} (hτ : Maj B H τ.poly)
    {l : List Poly} (hl : ∀ f ∈ l, Maj B k f) (w : ℕ) : Maj B (H + k + 1) (τ.callList l w) := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  refine Maj.bind₁ hB hτ fun i _ => ?_
  unfold callSubst
  split_ifs with hi
  · show Maj B k (l.getD i 0)
    by_cases hil : i < l.length
    · rw [List.getD_eq_getElem _ _ hil]
      exact hl _ (List.getElem_mem hil)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Maj.zero _ hB1
  · exact (Maj.X _).mono (Nat.zero_le _) hB1

/-- The callee of operation `op` of a model-evaluation recipe. -/
noncomputable def opCallee (templates recipes : List ExPoly) (r : ModelRecipe) :
    Operation → ExPoly
  | .add .. => getEx templates r.addition
  | .mul .. => getEx templates r.multiplication
  | .power .. => match r.power with
    | some i => getEx recipes i
    | none => ExPoly.empty

/-- The height of the callee of operation `op`. -/
def opHeight (tH rH : List ℕ) (r : ModelRecipe) : Operation → ℕ
  | .add .. => tH.getD r.addition 0
  | .mul .. => tH.getD r.multiplication 0
  | .power .. => match r.power with
    | some i => rH.getD i 0
    | none => 0

/-- **Model-evaluation recipes satisfy the height majorant.** -/
theorem model_majorant (hB : 2 ^ 20 ≤ B) (templates recipes : List ExPoly) (tH rH : List ℕ)
    (r : ModelRecipe) (hlen : (r.conjuncts templates recipes).length ≤ B)
    (hsrc : ∀ row ∈ r.sources, row.2.isSome →
      Maj B (tH.getD r.natural 0) (getEx templates r.natural).poly)
    (hconst : ∀ d ∈ r.constants, Maj B (tH.getD d.1 0) (getEx templates d.1).poly)
    (hops : ∀ op ∈ r.operations, Maj B (opHeight tH rH r op) (opCallee templates recipes r op).poly) :
    Maj B (recipeHeight tH rH (.model r)) ((Recipe.model r).denote templates recipes).poly := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  set H := max 4 (listMax ((modelCalleeHeights tH rH r).map (· + 3))) with hH
  have h4 : 4 ≤ H := le_max_left _ _
  have hcallee : ∀ h ∈ modelCalleeHeights tH rH r, h + 3 ≤ H := fun h hh =>
    (le_listMax (l := (modelCalleeHeights tH rH r).map (· + 3))
      (List.mem_map.2 ⟨h, hh, rfl⟩)).trans (le_max_right _ _)
  have hcall : ∀ {τ : ExPoly} {hκ : ℕ}, Maj B hκ τ.poly → hκ ∈ modelCalleeHeights tH rH r →
      ∀ (l : List Poly), (∀ f ∈ l, Maj B 1 f) → ∀ w, Maj B H (τ.callList l w) := by
    intro τ hκ hτ hmem l hl w
    exact (Maj.callList hB hτ hl w).mono (by have := hcallee hκ hmem; omega) hB1
  have hrefs : ∀ (a b : ℤ), ∀ f ∈ pointRefList r.generator a ++ pointRefList r.generator b,
      Maj B 1 f := by
    intro a b f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact maj_mem_pointRefList hB _ a f hf
    · exact maj_mem_pointRefList hB _ b f hf
  have hconj : ∀ φ ∈ r.conjuncts templates recipes, Maj B H φ.compile := by
    intro φ hφ
    simp only [ModelRecipe.conjuncts, List.mem_append, List.mem_map, List.mem_filterMap] at hφ
    rcases hφ with ((((⟨f, hf, rfl⟩ | ⟨row, hrow, hφ⟩) | ⟨d, hd, rfl⟩) | ⟨op, hop, rfl⟩) |
      ⟨f, hf, rfl⟩)
    · -- generator constraints
      rw [Formula.compile_atom]
      refine Maj.mono ?_ (by omega : 1 ≤ H) hB1
      simp only [generatorConstraints, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact (((Scale.ofNat hB1 8 (by norm_num)).mul (Scale.X hB1 _)).sub
          (Scale.ofNat hB1 1641 (by norm_num)) hB1 (s := 6)).maj_one
          (two_pow_le_pow_eight hB (by norm_num))
      · exact (((Scale.ofNat hB1 4 (by norm_num)).mul (Scale.X hB1 _)).add
          (Scale.ofNat hB1 15465 (by norm_num)) hB1 (s := 6)).maj_one
          (two_pow_le_pow_eight hB (by norm_num))
      · exact (((Scale.ofNat hB1 32 (by norm_num)).mul (Scale.X hB1 _)).sub
          (Scale.ofNat hB1 87483 (by norm_num)) hB1 (s := 6)).maj_one
          (two_pow_le_pow_eight hB (by norm_num))
    · -- natural calls of the source rows
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hφ
      rw [compile_callListFormula]
      have hsome : row.2.isSome := by rw [hs]; rfl
      refine hcall (hsrc row hrow hsome) ?_ _ (maj_mem_pointRefList hB _ row.1) s
      simp only [modelCalleeHeights, List.mem_append, List.mem_filterMap]
      exact Or.inl (Or.inl ⟨row, hrow, by rw [hs]; rfl⟩)
    · -- constant definitions
      rw [compile_callListFormula]
      refine hcall (hconst d hd) ?_ _ (hrefs _ _) d.2.2
      simp only [modelCalleeHeights, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨d, hd, rfl⟩)
    · -- operations
      have hmem : opHeight tH rH r op ∈ modelCalleeHeights tH rH r := by
        simp only [modelCalleeHeights, List.mem_append, List.mem_map]
        refine Or.inr ⟨op, hop, ?_⟩
        cases op <;> rfl
      have hτ := hops op hop
      cases op with
      | add a b o s =>
        rw [compile_callListFormula]
        exact hcall hτ hmem _ (fun f hf => by
          rcases List.mem_append.1 hf with hf | hf
          · exact hrefs a b f hf
          · exact maj_mem_pointRefList hB _ o f hf) s
      | mul a b o s =>
        rw [compile_callListFormula]
        exact hcall hτ hmem _ (fun f hf => by
          rcases List.mem_append.1 hf with hf | hf
          · exact hrefs a b f hf
          · exact maj_mem_pointRefList hB _ o f hf) s
      | power a b c o s =>
        rw [compile_callListFormula]
        refine hcall (τ := opCallee templates recipes r (.power a b c o s)) hτ hmem _
          (fun f hf => ?_) s
        rcases List.mem_append.1 hf with hf | hf
        · rcases List.mem_append.1 hf with hf | hf
          · exact hrefs a b f hf
          · exact maj_mem_pointRefList hB _ c f hf
        · exact maj_mem_pointRefList hB _ o f hf
    · -- root differences
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      rw [Formula.compile_atom]
      refine Maj.mono ?_ (by omega : 1 ≤ H) hB1
      exact ((sz_pointRef hB1 _ _ i).sub (sz_pointRef hB1 _ _ i) hB1).maj_one
        (two_pow_le_pow_eight hB (by norm_num))
  show Maj B (H + 2) (Connective.sumSq.apply (r.constraints templates recipes))
  refine Maj.sum_sq hB _ (by rw [ModelRecipe.constraints, List.length_map]; exact hlen) ?_
  intro c hc
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hc
  exact hconj φ hφ

/-- **Composition recipes satisfy the height majorant.** -/
theorem composition_majorant (hB : 2 ^ 20 ≤ B) (templates recipes : List ExPoly)
    (tH rH : List ℕ) (r : CompositionRecipe) (hlen : r.calls.length ≤ B)
    (hcall : ∀ c ∈ r.calls,
      Maj B (callTargetHeight tH rH c.target) (c.target.resolve templates recipes).poly) :
    Maj B (recipeHeight tH rH (.composition r))
      ((Recipe.composition r).denote templates recipes).poly := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  set H := listMax (r.calls.map fun c => callTargetHeight tH rH c.target)
  have hc : ∀ f ∈ r.constraints templates recipes, Maj B H f := by
    intro f hf
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
    rw [RecipeCall.constraint_eq]
    refine (Maj.bind₁_of_maj_zero (hcall c hc) fun i _ => ?_).mono
      (le_listMax (List.mem_map.2 ⟨c, hc, rfl⟩)) hB1
    unfold callSubst
    split_ifs with hi
    · show Maj B 0 ((c.args.map X).getD i 0)
      by_cases hia : i < c.args.length
      · rw [List.getD_eq_getElem _ _ (by simpa using hia), List.getElem_map]
        exact Maj.X _
      · rw [List.getD_eq_default _ _ (by simpa using hia)]
        exact Maj.zero _ hB1
    · exact Maj.X _
  have hlen' : (r.constraints templates recipes).length ≤ B := by
    rw [CompositionRecipe.constraints, List.length_map]; exact hlen
  show Maj B (H + match r.connective with | .sumSq => 2 | .prod => 1)
    (r.connective.apply (r.constraints templates recipes))
  cases r.connective with
  | sumSq => exact Maj.sum_sq hB _ hlen' hc
  | prod => exact Maj.prod hB _ hlen' hc

end ZInQ.Size
