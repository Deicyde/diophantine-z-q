import ZInQKernel.Syntax.Recipes.Precision
import ZInQKernel.Syntax.Recipes.Scope
import ZInQKernel.Syntax.Recipes.Arith

/-!
# Witness accounting of the specified polynomial

Blueprint: `syntax/recipes/witness-accounting.md`.

The seven recipes in their order `power_value, precision, close, main, value_union, value,
integers` (`specRecipes N c₃`), each composition recipe instantiated with the witness count of
the recipe it calls, and their denotations over the template library (`specLib`).

* Counts. `power_value` has `20` parameters and `17786718` variables
  (`powerValueRecipe_variableCount`); the composition counts are explicit in the witness count
  `w_prec` of `precision` (`specClose_variableCount`, …), and with the shape of the natural
  precision circuit `integers` has at most `292890231905` variables
  (`specIntegers_variableCount_le`). The counts are proved symbolically; no recipe is ever
  evaluated.
* Ranges. Every recipe denotation is well formed: all variables of its polynomial lie below its
  variable count (`specLib_wf`). In particular every variable of `[[integers]]` is among
  `X_0, …, X_{292890231904}` (`vars_integers_lt`).

The blueprint states exact counts and the disjointness of the private blocks; here the counts
are upper bounds, which is all the variable format of the target needs (exact equalities follow
in the same way from the exact shape), and the disjointness of blocks is not needed for the
variable bound (the compiler and assembly chapters prove the relational forms they use).
-/

namespace ZInQ.Syntax

open ZInQ.Compiler.Natural

/-- The witness count of a recipe. -/
def Recipe.witnessCount (ρ : Recipe) : ℕ := ρ.variableCount - ρ.parameterCount

@[simp] theorem Recipe.denote_witnesses (templates recipes : List ExPoly) (ρ : Recipe) :
    (ρ.denote templates recipes).witnesses = ρ.witnessCount := rfl

@[simp] theorem Recipe.denote_params (templates recipes : List ExPoly) (ρ : Recipe) :
    (ρ.denote templates recipes).params = ρ.parameterCount := rfl

/-! ### The recipes -/

section Recipes

variable (N : NatCircuit) (c3 : ℤ)

/-- `precision` as a recipe. -/
noncomputable def specPrecision : Recipe := .model (precisionRecipe N c3)

/-- `close`, calling `precision`. -/
noncomputable def specClose : Recipe := .composition (closeRecipe (specPrecision N c3).witnessCount)

/-- `main`, calling `close`. -/
noncomputable def specMain : Recipe := .composition (mainRecipe (specClose N c3).witnessCount)

/-- `value_union`, calling `main`. -/
noncomputable def specValueUnion : Recipe :=
  .composition (valueUnionRecipe (specMain N c3).witnessCount)

/-- `value`, calling `value_union`. -/
noncomputable def specValue : Recipe := .composition (valueRecipe (specValueUnion N c3).witnessCount)

/-- `integers`, calling `value`. -/
noncomputable def specIntegers : Recipe :=
  .composition (integersRecipe (specValue N c3).witnessCount)

/-- **The recipes of the specification**, in dependency order (indices `0, …, 6`). -/
noncomputable def specRecipes : List Recipe :=
  [.model powerValueRecipe, specPrecision N c3, specClose N c3, specMain N c3,
    specValueUnion N c3, specValue N c3, specIntegers N c3]

theorem length_specRecipes : (specRecipes N c3).length = 7 := rfl

end Recipes

/-! ### Counts -/

section Counts

variable (N : NatCircuit) (c3 : ℤ)

theorem specClose_variableCount :
    (specClose N c3).variableCount = 703321 + (specPrecision N c3).witnessCount + 53 :=
  closeRecipe_variableCount _

theorem specMain_variableCount :
    (specMain N c3).variableCount = 11 + (specClose N c3).witnessCount + 35282 :=
  mainRecipe_variableCount _

theorem specValueUnion_variableCount :
    (specValueUnion N c3).variableCount = 412 + (specMain N c3).witnessCount :=
  valueUnionRecipe_variableCount _

theorem specValue_variableCount :
    (specValue N c3).variableCount = 13 + (specValueUnion N c3).witnessCount :=
  valueRecipe_variableCount _

theorem specIntegers_variableCount :
    (specIntegers N c3).variableCount = 6 + (specValue N c3).witnessCount :=
  integersRecipe_variableCount _

theorem specIntegers_parameterCount : (specIntegers N c3).parameterCount = 1 :=
  integersRecipe_parameterCount _

theorem specValue_parameterCount : (specValue N c3).parameterCount = 6 :=
  valueRecipe_parameterCount _

theorem specClose_witnessCount :
    (specClose N c3).witnessCount = 703310 + (specPrecision N c3).witnessCount + 53 := by
  rw [Recipe.witnessCount.eq_def (specClose N c3)]
  rw [specClose_variableCount, show (specClose N c3).parameterCount = 11 from
    closeRecipe_parameterCount _]
  omega

theorem specMain_witnessCount :
    (specMain N c3).witnessCount = 5 + (specClose N c3).witnessCount + 35282 := by
  rw [Recipe.witnessCount.eq_def (specMain N c3)]
  rw [specMain_variableCount, show (specMain N c3).parameterCount = 6 from
    mainRecipe_parameterCount _]
  omega

theorem specValueUnion_witnessCount :
    (specValueUnion N c3).witnessCount = 406 + (specMain N c3).witnessCount := by
  rw [Recipe.witnessCount.eq_def (specValueUnion N c3)]
  rw [specValueUnion_variableCount, show (specValueUnion N c3).parameterCount = 6 from
    valueUnionRecipe_parameterCount _]
  omega

theorem specValue_witnessCount :
    (specValue N c3).witnessCount = 7 + (specValueUnion N c3).witnessCount := by
  rw [Recipe.witnessCount.eq_def (specValue N c3)]
  rw [specValue_variableCount, specValue_parameterCount]
  omega

/-- `integers` has `739069` variables more than `precision` has witnesses:
`5 + 7 + 406 + 5 + 35282 + 8·5 + 5·140654 + 53 + 1 = 739069`. -/
theorem specIntegers_variableCount_eq :
    (specIntegers N c3).variableCount = 739069 + (specPrecision N c3).witnessCount := by
  rw [specIntegers_variableCount, specValue_witnessCount, specValueUnion_witnessCount,
    specMain_witnessCount, specClose_witnessCount]
  omega

/-- **The witness count of the specified polynomial.** Under the shape of the natural precision
circuit, `integers` has at most `292890231905` variables: one input and at most `292890231904`
witnesses. -/
theorem specIntegers_variableCount_le {N : NatCircuit} {c3 : ℤ} (hN : PrecisionShape N c3) :
    (specIntegers N c3).variableCount ≤ 292890231905 := by
  rw [specIntegers_variableCount_eq]
  have := precisionRecipe_variableCount_le hN
  simp only [specPrecision, Recipe.witnessCount, Recipe.variableCount, Recipe.parameterCount,
    precisionRecipe_parameterCount, hN.inputCount] at this ⊢
  omega

end Counts

/-! ### The template library -/

section Library

variable {E : Type} (I : Constructors E) (cstar ell T c3 : ℤ)

theorem getEx_wf_of_forall {lib : List ExPoly} (h : ∀ τ ∈ lib, τ.WF) (j : ℕ) : (getEx lib j).WF := by
  unfold getEx
  rw [List.getD_eq_getElem?_getD]
  cases hj : lib[j]? with
  | none => exact ExPoly.empty_wf
  | some τ => exact h τ (List.mem_of_getElem? hj)

theorem getEx_witnesses (lib : List ExPoly) (j : ℕ) :
    (getEx lib j).witnesses = (lib.map ExPoly.witnesses).getD j 0 := by
  unfold getEx
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases lib[j]? <;> rfl

theorem templateLibrary_getEx_wf (j : ℕ) : (getEx (templateLibrary I cstar ell T c3) j).WF :=
  getEx_wf_of_forall (templateLibrary_wf I cstar ell T c3) j

theorem templateLibrary_getEx_witnesses (j : ℕ) :
    (getEx (templateLibrary I cstar ell T c3) j).witnesses =
      [7, 6, 1, 0, 0, 11, 162, 1298, 35106, 1, 1, 35134, 140604, 140654, 4, 53, 35282, 406,
        1, 1, 1, 1, 1].getD j 0 := by
  rw [getEx_witnesses, templateLibrary_witnesses]

theorem templateLibrary_scalar_witnesses_le (h : ℕ) :
    (getEx (templateLibrary I cstar ell T c3) (18 + h)).witnesses ≤ 1 := by
  rw [templateLibrary_getEx_witnesses]
  rcases Nat.lt_or_ge h 5 with hh | hh
  · interval_cases h <;> decide
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    omega

end Library

/-! ### Ranges of the composition recipes -/

section Compositions

variable (templates recipes : List ExPoly)

theorem mem_point {a j : ℕ} : j ∈ point a ↔ a ≤ j ∧ j < a + 5 := by
  simp only [point, List.mem_range'_1]

theorem closeRecipe_inRange (w : ℕ) (h13 : (getEx templates 13).WF)
    (h13w : (getEx templates 13).witnesses = 140654) (h15 : (getEx templates 15).WF)
    (h15w : (getEx templates 15).witnesses = 53) (h1 : (getEx recipes 1).WF)
    (h1w : (getEx recipes 1).witnesses = w) : (closeRecipe w).InRange templates recipes := by
  refine ⟨by rw [closeRecipe_parameterCount, closeRecipe_variableCount]; omega, ?_⟩
  rw [closeRecipe_calls, closeRecipe_variableCount]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [CallTarget.resolve, h13w, h15w, h1w] <;>
    refine ⟨by assumption, fun j hj => ?_, by omega⟩ <;>
    simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega

theorem mainRecipe_inRange (w : ℕ) (h16 : (getEx templates 16).WF)
    (h16w : (getEx templates 16).witnesses = 35282) (h2 : (getEx recipes 2).WF)
    (h2w : (getEx recipes 2).witnesses = w) : (mainRecipe w).InRange templates recipes := by
  refine ⟨by rw [mainRecipe_parameterCount, mainRecipe_variableCount]; omega, ?_⟩
  rw [mainRecipe_calls, mainRecipe_variableCount]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
    simp only [CallTarget.resolve, h16w, h2w] <;>
    refine ⟨by assumption, fun j hj => ?_, by omega⟩ <;>
    simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega

theorem valueUnionRecipe_inRange (w : ℕ) (h17 : (getEx templates 17).WF)
    (h17w : (getEx templates 17).witnesses = 406) (h3 : (getEx recipes 3).WF)
    (h3w : (getEx recipes 3).witnesses = w) : (valueUnionRecipe w).InRange templates recipes := by
  refine ⟨by rw [valueUnionRecipe_parameterCount, valueUnionRecipe_variableCount]; omega, ?_⟩
  rw [valueUnionRecipe_calls, valueUnionRecipe_variableCount]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
    simp only [CallTarget.resolve, h17w, h3w] <;>
    refine ⟨by assumption, fun j hj => ?_, by omega⟩ <;>
    simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega

theorem valueRecipe_inRange (w : ℕ) (h0 : (getEx templates 0).WF)
    (h0w : (getEx templates 0).witnesses = 7) (h4 : (getEx recipes 4).WF)
    (h4w : (getEx recipes 4).witnesses = w) : (valueRecipe w).InRange templates recipes := by
  refine ⟨by rw [valueRecipe_parameterCount, valueRecipe_variableCount]; omega, ?_⟩
  rw [valueRecipe_calls, valueRecipe_variableCount]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
    simp only [CallTarget.resolve, h0w, h4w] <;>
    refine ⟨by assumption, fun j hj => ?_, by omega⟩ <;>
    simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega

theorem integersRecipe_inRange (w : ℕ) (h5 : (getEx recipes 5).WF)
    (h5w : (getEx recipes 5).witnesses = w) : (integersRecipe w).InRange templates recipes := by
  refine ⟨by rw [integersRecipe_parameterCount, integersRecipe_variableCount]; omega, ?_⟩
  rw [integersRecipe_calls, integersRecipe_variableCount]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [CallTarget.resolve, h5w]
  refine ⟨by assumption, fun j hj => ?_, by omega⟩
  simp only [List.mem_append, mem_point, List.mem_singleton] at hj
  omega

end Compositions

/-! ### The denotations -/

section Denotations

variable {E : Type} (I : Constructors E) (cstar ell T c3 : ℤ) (N : NatCircuit)

/-- **The denotations of the seven recipes** over the template library. -/
noncomputable def specLib : List ExPoly :=
  denoteRecipes (templateLibrary I cstar ell T c3) (specRecipes N c3)

theorem getEx_denoteRecipes_take (templates : List ExPoly) (rs : List Recipe) {i j : ℕ}
    (hj : j < i) (hi : i ≤ rs.length) :
    getEx (denoteRecipes templates (rs.take i)) j = getEx (denoteRecipes templates rs) j := by
  have hj' : j < (rs.take i).length := by simp; omega
  rw [getEx_denoteRecipes _ _ hj', getEx_denoteRecipes _ _ (by omega), List.getElem_take,
    List.take_take, Nat.min_eq_left hj.le]

theorem getEx_specLib {i : ℕ} (hi : i < 7) :
    getEx (specLib I cstar ell T c3 N) i = (specRecipes N c3)[i].denote
      (templateLibrary I cstar ell T c3)
      (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take i)) :=
  getEx_denoteRecipes _ _ hi

theorem getEx_specLib_take {i j : ℕ} (hj : j < i) (hi : i ≤ 7) :
    getEx (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take i)) j =
      getEx (specLib I cstar ell T c3 N) j :=
  getEx_denoteRecipes_take _ _ hj hi

theorem getEx_specLib_witnesses {i : ℕ} (hi : i < 7) :
    (getEx (specLib I cstar ell T c3 N) i).witnesses = ((specRecipes N c3)[i]).witnessCount := by
  rw [getEx_specLib I cstar ell T c3 N hi]
  rfl

/-- The library conditions of the translation. -/
theorem translate_inRange_lib (recipes : List ExPoly) (consts : List ℤ) (C : NatCircuit)
    (mode : OutputMode) (natInputs : Bool) (power : Option (ℕ × ℕ))
    (hπ : ∀ i w, power = some (i, w) → (getEx recipes i).WF ∧ (getEx recipes i).witnesses ≤ w) :
    (translate consts C mode natInputs power).InRange (templateLibrary I cstar ell T c3) recipes :=
  translate_inRange _ _ _ _ _ _ _ (templateLibrary_getEx_wf I cstar ell T c3)
    (by rw [templateLibrary_getEx_witnesses]; decide)
    (by rw [templateLibrary_getEx_witnesses]; decide)
    (by rw [templateLibrary_getEx_witnesses]; decide)
    (templateLibrary_scalar_witnesses_le I cstar ell T c3) hπ

theorem specLib_wf_0 : (getEx (specLib I cstar ell T c3 N) 0).WF := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  exact ModelRecipe.denote_wf (translate_inRange_lib I cstar ell T c3 _ _ _ _ _ _
    (fun i w h => by cases h))

theorem specLib_wf_1 : (getEx (specLib I cstar ell T c3 N) 1).WF := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine ModelRecipe.denote_wf (translate_inRange_lib I cstar ell T c3 _ _ _ _ _ _ ?_)
  intro i w h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
  refine ⟨specLib_wf_0 I cstar ell T c3 N, ?_⟩
  rw [getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
  rfl

theorem specLib_wf_2 : (getEx (specLib I cstar ell T c3 N) 2).WF := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine CompositionRecipe.denote_wf (closeRecipe_inRange _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 13) (by rw [templateLibrary_getEx_witnesses]; rfl)
    (templateLibrary_getEx_wf I cstar ell T c3 15) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_)
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_1 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_wf_3 : (getEx (specLib I cstar ell T c3 N) 3).WF := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine CompositionRecipe.denote_wf (mainRecipe_inRange _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 16) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_)
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_2 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_wf_4 : (getEx (specLib I cstar ell T c3 N) 4).WF := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine CompositionRecipe.denote_wf (valueUnionRecipe_inRange _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 17) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_)
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_3 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_wf_5 : (getEx (specLib I cstar ell T c3 N) 5).WF := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine CompositionRecipe.denote_wf (valueRecipe_inRange _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 0) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_)
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_4 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_wf_6 : (getEx (specLib I cstar ell T c3 N) 6).WF := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine CompositionRecipe.denote_wf (integersRecipe_inRange _ _ _ ?_ ?_)
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_5 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

/-- **Witness scope of the specified recipes** (variable ranges): every recipe denotation is well
formed. -/
theorem specLib_wf : ∀ τ ∈ specLib I cstar ell T c3 N, τ.WF := by
  intro τ hτ
  have hlen : (specLib I cstar ell T c3 N).length = 7 := by
    rw [specLib, denoteRecipes]
    simp [specRecipes]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hτ
  have h : (specLib I cstar ell T c3 N)[i] = getEx (specLib I cstar ell T c3 N) i := by
    simp [getEx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [h]
  rw [hlen] at hi
  interval_cases i
  · exact specLib_wf_0 I cstar ell T c3 N
  · exact specLib_wf_1 I cstar ell T c3 N
  · exact specLib_wf_2 I cstar ell T c3 N
  · exact specLib_wf_3 I cstar ell T c3 N
  · exact specLib_wf_4 I cstar ell T c3 N
  · exact specLib_wf_5 I cstar ell T c3 N
  · exact specLib_wf_6 I cstar ell T c3 N

/-- The denotation of `integers`: one parameter, the variable count of `integers`. -/
theorem getEx_specLib_six :
    getEx (specLib I cstar ell T c3 N) 6 = (specIntegers N c3).denote
      (templateLibrary I cstar ell T c3)
      (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take 6)) :=
  getEx_specLib I cstar ell T c3 N (by decide)

/-- **Every variable of `[[integers]]` lies below `292890231905`**, given the shape of the
natural precision circuit. -/
theorem vars_integers_lt {N : NatCircuit} {c3 : ℤ} (hN : PrecisionShape N c3) :
    VarsLT (getEx (specLib I cstar ell T c3 N) 6).poly 292890231905 := by
  refine VarsLT.mono (specLib_wf_6 I cstar ell T c3 N) ?_
  rw [getEx_specLib_six]
  simp only [ExPoly.varCount, Recipe.denote_params, Recipe.denote_witnesses, Recipe.witnessCount,
    specIntegers_parameterCount]
  have := specIntegers_variableCount_le hN
  have h1 : 1 ≤ (specIntegers N c3).variableCount := by
    rw [specIntegers_variableCount]; omega
  omega

end Denotations

end ZInQ.Syntax
