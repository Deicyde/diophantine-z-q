import ZInQKernel.Size.Majorants.TemplateHeights
import ZInQKernel.Size.Majorants.RecipeMajorant
import ZInQKernel.Syntax.Recipes

/-!
# Recipe heights

Blueprint: `size/majorants/recipe-heights.md`.

For an admissible bound `B` (`LibraryAdmissible`) and a natural precision circuit with the
shape of the compiler chapter (`PrecisionShape N c₃`), the seven recipes of the specification
satisfy the majorant at the heights `228, 233, 235, 251, 252, 254, 256` (`recipe_heights`).

The two model-evaluation recipes are translations of natural circuits. Their conjuncts are
counted from the translation, without evaluating it: `power_value` has
`8 + 79 + 3 + 196 + 190 = 476` conjuncts (`powerValueRecipe_conjuncts_length`) and `precision`
at most `8 + 54056 + 4 + 125327 + 98382 + 15845 = 293622 ≤ 2^20`
(`precisionRecipe_conjuncts_length_le`); their constant definitions call the fixed-scalar
templates `18, …` (`translate_constants_ge`), of tabulated height `17`.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax ZInQ.Compiler.Natural

/-! ### Counts of a translation -/

/-- The number of conjuncts of a model-evaluation recipe. -/
theorem length_conjuncts (templates recipes : List ExPoly) (r : ModelRecipe) :
    (r.conjuncts templates recipes).length =
      8 + r.sources.countP (fun row => row.2.isSome) + r.constants.length +
        r.operations.length := by
  simp only [ModelRecipe.conjuncts, List.length_append, List.length_map, generatorConstraints,
    List.length_ofFn, List.length_cons, List.length_nil, List.length_filterMap_eq_countP,
    Option.isSome_map]
  omega

theorem foldl_trVar_counts (k : ℕ) (nat : Bool) (l : List (ℕ × VarKind)) (s : TrState) :
    (l.foldl (trVar k nat) s).sources.countP (fun row => row.2.isSome) =
        s.sources.countP (fun row => row.2.isSome) +
          l.countP (fun v => !decide (IsInputVar k v) || nat) ∧
      (l.foldl (trVar k nat) s).constants = s.constants ∧
      (l.foldl (trVar k nat) s).operations = s.operations := by
  induction l generalizing s with
  | nil => simp
  | cons v l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (trVar k nat s v)
    rw [List.foldl_cons, h1, h2, h3]
    refine ⟨?_, rfl, rfl⟩
    simp only [trVar, List.countP_append, List.countP_cons, List.countP_nil]
    by_cases h : !decide (IsInputVar k v) || nat <;> simp [h]; omega

/-- The number of operations of a node: one for an addition, multiplication or call. -/
def opCount : NatNode → ℕ
  | .add _ _ => 1
  | .mul _ _ => 1
  | .call _ _ _ _ => 1
  | _ => 0

theorem sum_opCount (l : List NatNode) :
    (l.map opCount).sum = l.countP NatNode.isAdd + l.countP NatNode.isMul +
      l.countP NatNode.isCall := by
  induction l with
  | nil => simp
  | cons n l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases n <;> simp [opCount, NatNode.isAdd, NatNode.isMul, NatNode.isCall] <;> omega

theorem trNode_counts (consts : List ℤ) (W : ℕ) (s : TrState) (n : NatNode) :
    (trNode consts W s n).sources = s.sources ∧
      (trNode consts W s n).operations.length = s.operations.length + opCount n ∧
      (trNode consts W s n).constants.length + s.constRefs.length =
        s.constants.length + (trNode consts W s n).constRefs.length ∧
      ∀ d ∈ (trNode consts W s n).constants, d ∈ s.constants ∨ 18 ≤ d.1 := by
  cases n with
  | const c =>
    simp only [trNode, opCount]
    split_ifs
    · split
      · exact ⟨rfl, by simp, by simp, fun d hd => Or.inl hd⟩
      · refine ⟨rfl, by simp, by simp; omega, fun d hd => ?_⟩
        rcases List.mem_append.1 hd with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h; subst h; exact Or.inr (by simp)
    · exact ⟨rfl, by simp, by simp, fun d hd => Or.inl hd⟩
  | var i => exact ⟨rfl, by simp [trNode, opCount], by simp [trNode], fun d hd => Or.inl hd⟩
  | add a b => exact ⟨rfl, by simp [trNode, opCount], by simp [trNode], fun d hd => Or.inl hd⟩
  | mul a b => exact ⟨rfl, by simp [trNode, opCount], by simp [trNode], fun d hd => Or.inl hd⟩
  | call a b c w =>
    exact ⟨rfl, by simp [trNode, opCount], by simp [trNode], fun d hd => Or.inl hd⟩

theorem foldl_trNode_counts (consts : List ℤ) (W : ℕ) (l : List NatNode) (s : TrState) :
    (l.foldl (trNode consts W) s).sources = s.sources ∧
      (l.foldl (trNode consts W) s).operations.length =
        s.operations.length + (l.map opCount).sum ∧
      (l.foldl (trNode consts W) s).constants.length + s.constRefs.length =
        s.constants.length + (l.foldl (trNode consts W) s).constRefs.length ∧
      ∀ d ∈ (l.foldl (trNode consts W) s).constants, d ∈ s.constants ∨ 18 ≤ d.1 := by
  induction l generalizing s with
  | nil => exact ⟨rfl, by simp, rfl, fun d hd => Or.inl hd⟩
  | cons n l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := trNode_counts consts W s n
    obtain ⟨k1, k2, k3, k4⟩ := ih (trNode consts W s n)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    refine ⟨k1.trans h1, by rw [k2, h2]; ring, by omega, fun d hd => ?_⟩
    rcases k4 d hd with h | h
    · exact h4 d h
    · exact Or.inr h

/-- **The number of conjuncts of a translation**: the generator constraints and root
differences, one natural call for each constrained explicit variable, one constant definition
for each distinct nontrivial constant, one operation for each addition, multiplication and call
node. -/
theorem translate_conjuncts_length (consts : List ℤ) (N : NatCircuit) (mode : OutputMode)
    (nat : Bool) (power : Option (ℕ × ℕ)) (templates recipes : List ExPoly) :
    ((translate consts N mode nat power).conjuncts templates recipes).length =
      8 + N.explicitVars.countP (fun v => !decide (IsInputVar N.inputCount v) || nat) +
        (N.nodes.filterMap nontrivialConst).toFinset.card + (N.nodes.map opCount).sum := by
  rw [length_conjuncts]
  set W := (power.map Prod.snd).getD 0
  obtain ⟨v1, v2, v3⟩ := foldl_trVar_counts N.inputCount nat N.explicitVars
    ⟨trParams N.inputCount mode + 3, [], [], [], [], [], []⟩
  have hc : (trVarsState N mode nat).constRefs = [] := foldl_trVar_constRefs _ _ _ _
  have h0 : ((trVarsState N mode nat).constRefs.map Prod.fst).Nodup := by
    rw [hc]; exact List.nodup_nil
  obtain ⟨-, k2, k3⟩ := foldl_trNode consts W N.nodes _ h0
  obtain ⟨n1, n2, n3, -⟩ := foldl_trNode_counts consts W N.nodes (trVarsState N mode nat)
  rw [hc] at k3
  have hlen : ((N.nodes.foldl (trNode consts W) (trVarsState N mode nat)).constRefs.map
      Prod.fst).length = (N.nodes.filterMap nontrivialConst).toFinset.card := by
    rw [← List.toFinset_card_of_nodup k2]
    congr 1
    ext c
    simp [k3]
  rw [List.length_map] at hlen
  have e1 : (translate consts N mode nat power).sources =
      (N.nodes.foldl (trNode consts W) (trVarsState N mode nat)).sources := rfl
  have e2 : (translate consts N mode nat power).constants =
      (N.nodes.foldl (trNode consts W) (trVarsState N mode nat)).constants := rfl
  have e3 : (translate consts N mode nat power).operations =
      (N.nodes.foldl (trNode consts W) (trVarsState N mode nat)).operations := rfl
  have hv1 : (trVarsState N mode nat).sources.countP (fun row => row.2.isSome) =
      N.explicitVars.countP (fun v => !decide (IsInputVar N.inputCount v) || nat) := by
    rw [trVarsState, v1]; simp
  have hv2 : (trVarsState N mode nat).constants = [] := by rw [trVarsState, v2]
  have hv3 : (trVarsState N mode nat).operations = [] := by rw [trVarsState, v3]
  rw [e1, e2, e3, n1, n2, hv1, hv3, List.length_nil, zero_add]
  rw [hc, hv2, List.length_nil, List.length_nil, add_zero, zero_add, hlen] at n3
  rw [n3]

/-- The constant definitions of a translation call the templates `18, …`. -/
theorem translate_constants_ge (consts : List ℤ) (N : NatCircuit) (mode : OutputMode)
    (nat : Bool) (power : Option (ℕ × ℕ)) :
    ∀ d ∈ (translate consts N mode nat power).constants, 18 ≤ d.1 := by
  intro d hd
  obtain ⟨-, v2, -⟩ := foldl_trVar_counts N.inputCount nat N.explicitVars
    ⟨trParams N.inputCount mode + 3, [], [], [], [], [], []⟩
  have hv2 : (trVarsState N mode nat).constants = [] := by rw [trVarsState, v2]
  obtain ⟨-, -, -, n4⟩ := foldl_trNode_counts consts ((power.map Prod.snd).getD 0) N.nodes
    (trVarsState N mode nat)
  rcases n4 d hd with h | h
  · simp [hv2] at h
  · exact h

theorem sum_varCost_false (k : ℕ) (l : List (ℕ × VarKind)) :
    (l.map (varCost k false)).sum =
      (5 + 140604) * l.countP (fun v => !decide (IsInputVar k v) || false) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases hv : IsInputVar k v <;> simp [varCost, hv]; ring

/-- `power_value` has `476` conjuncts. -/
theorem powerValueRecipe_conjuncts_length (templates recipes : List ExPoly) :
    (powerValueRecipe.conjuncts templates recipes).length = 476 := by
  obtain ⟨h1, -, h3⟩ := powerTemplateCircuit_translationStats
  have hs := ZInQ.Compiler.Universal.powerTemplate_nodeStats
  simp only [Prod.mk.injEq] at hs
  obtain ⟨-, -, hadd, hmul, hcall, -⟩ := hs
  have hc : powerTemplateCircuit.explicitVars.countP
      (fun v => !decide (IsInputVar 3 v) || false) = 79 := by
    have h1' := (sum_varCost_false 3 powerTemplateCircuit.explicitVars).symm.trans h1
    omega
  have hk : powerTemplateCircuit.inputCount = 3 := rfl
  rw [powerValueRecipe, translate_conjuncts_length, hk, hc, sum_opCount, ← countKind_add,
    ← countKind_mul, ← ZInQ.Compiler.Universal.countKind_call, hadd, hmul, hcall, h3]
  decide

/-- `precision` has at most `293622` conjuncts. -/
theorem precisionRecipe_conjuncts_length_le {N : NatCircuit} {c3 : ℤ} (hN : PrecisionShape N c3)
    (templates recipes : List ExPoly) :
    ((precisionRecipe N c3).conjuncts templates recipes).length ≤ 293622 := by
  rw [precisionRecipe, translate_conjuncts_length, sum_opCount]
  have h1 := List.countP_le_length (p := fun v => !decide (IsInputVar N.inputCount v) || true)
    (l := N.explicitVars)
  have h2 := card_le_of_forall_mem hN.consts
  have := hN.explicitVars_length
  have := hN.adds
  have := hN.muls
  have := hN.calls
  omega

/-! ### Heights of the model-evaluation recipes -/

variable {E : Type} {B : ℕ}

theorem templateHeightTable_ge_eighteen : ∀ i, 18 ≤ i → templateHeightTable.getD i 0 ≤ 17 := by
  intro i hi
  rcases Nat.lt_or_ge i 23 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [templateHeightTable]; omega)]
    omega

theorem templateLibrary_maj_all {I : Constructors E} {cstar ell T c3 : ℤ}
    (h : LibraryAdmissible B I cstar ell T c3) (i : ℕ) :
    Maj B (templateHeightTable.getD i 0) (getEx (templateLibrary I cstar ell T c3) i).poly := by
  rcases Nat.lt_or_ge i 23 with hi | hi
  · exact templateLibrary_maj h i hi
  · rw [getEx, List.getD_eq_default (templateLibrary I cstar ell T c3) _
      (by rw [length_templateLibrary]; exact hi)]
    exact Maj.zero _ (one_le_of_two_pow_twenty_le h.two_pow_le)

/-- The callee heights of a model-evaluation recipe are at most `H` when those of its natural
template, its constant definitions and its operations are. -/
theorem modelCalleeHeights_le (tH rH : List ℕ) (r : ModelRecipe) {H : ℕ}
    (hnat : tH.getD r.natural 0 ≤ H) (hconst : ∀ d ∈ r.constants, tH.getD d.1 0 ≤ H)
    (hops : ∀ op ∈ r.operations, opHeight tH rH r op ≤ H) :
    ∀ x ∈ modelCalleeHeights tH rH r, x ≤ H := by
  intro x hx
  simp only [modelCalleeHeights, List.mem_append, List.mem_filterMap, List.mem_map] at hx
  rcases hx with (⟨row, -, hrow⟩ | ⟨d, hd, rfl⟩) | ⟨op, hop, rfl⟩
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hrow
    exact hnat
  · exact hconst d hd
  · have := hops op hop
    cases op <;> exact this

/-- A translated recipe with the operation templates of the library and power recipe of height
`Hπ` has height at most `max(4, max(223, 21, 214, 17, Hπ) + 3) + 2`. -/
theorem recipeHeight_translate_le (consts : List ℤ) (N : NatCircuit) (mode : OutputMode)
    (nat : Bool) (power : Option (ℕ × ℕ)) (rH : List ℕ) {Hπ : ℕ}
    (hπ : ∀ i, power.map Prod.fst = some i → rH.getD i 0 ≤ Hπ) :
    recipeHeight templateHeightTable rH (.model (translate consts N mode nat power)) ≤
      max 4 (max 223 Hπ + 3) + 2 := by
  refine Nat.add_le_add_right (max_le_max le_rfl (listMax_le fun y hy => ?_)) 2
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  refine Nat.add_le_add_right (modelCalleeHeights_le templateHeightTable rH _ ?_ ?_ ?_ x hx) 3
  · exact le_max_left _ _
  · intro d hd
    exact (templateHeightTable_ge_eighteen _ (translate_constants_ge _ _ _ _ _ d hd)).trans
      (by omega)
  · intro op _
    cases op with
    | add => exact (show templateHeightTable.getD 1 0 ≤ 223 by decide).trans (le_max_left _ _)
    | mul => exact (show templateHeightTable.getD 11 0 ≤ 223 by decide).trans (le_max_left _ _)
    | power =>
      show (match power.map Prod.fst with | some i => rH.getD i 0 | none => 0) ≤ _
      cases hp : power.map Prod.fst with
      | none => exact Nat.zero_le _
      | some i => exact (hπ i hp).trans (le_max_right _ _)

/-- The callees of the operations of a translated recipe. -/
theorem translate_hops {I : Constructors E} {cstar ell T c3 : ℤ}
    (h : LibraryAdmissible B I cstar ell T c3) (consts : List ℤ) (N : NatCircuit)
    (mode : OutputMode) (nat : Bool) (power : Option (ℕ × ℕ)) (recipes : List ExPoly)
    (rH : List ℕ) (hπ : ∀ i, power.map Prod.fst = some i → Maj B (rH.getD i 0) (getEx recipes i).poly) :
    ∀ op ∈ (translate consts N mode nat power).operations,
      Maj B (opHeight templateHeightTable rH (translate consts N mode nat power) op)
        (opCallee (templateLibrary I cstar ell T c3) recipes
          (translate consts N mode nat power) op).poly := by
  intro op _
  cases op with
  | add => exact templateLibrary_maj_all h 1
  | mul => exact templateLibrary_maj_all h 11
  | power =>
    show Maj B (match power.map Prod.fst with | some i => rH.getD i 0 | none => 0)
      (match power.map Prod.fst with
        | some i => getEx recipes i
        | none => ExPoly.empty).poly
    cases hp : power.map Prod.fst with
    | none => exact Maj.zero 0 (one_le_of_two_pow_twenty_le h.two_pow_le)
    | some i => exact hπ i hp

/-- The majorant for a translated recipe over the template library. -/
theorem translate_majorant {I : Constructors E} {cstar ell T c3 : ℤ}
    (h : LibraryAdmissible B I cstar ell T c3) (consts : List ℤ) (N : NatCircuit)
    (mode : OutputMode) (nat : Bool) (power : Option (ℕ × ℕ)) (recipes : List ExPoly)
    (rH : List ℕ) {Hπ : ℕ}
    (hπ : ∀ i, power.map Prod.fst = some i →
      rH.getD i 0 ≤ Hπ ∧ Maj B (rH.getD i 0) (getEx recipes i).poly)
    (hlen : ((translate consts N mode nat power).conjuncts (templateLibrary I cstar ell T c3)
      recipes).length ≤ B) :
    Maj B (max 4 (max 223 Hπ + 3) + 2)
      ((Recipe.model (translate consts N mode nat power)).denote
        (templateLibrary I cstar ell T c3) recipes).poly := by
  have hB1 := one_le_of_two_pow_twenty_le h.two_pow_le
  refine (model_majorant h.two_pow_le _ recipes templateHeightTable rH _ hlen
    (fun _ _ _ => templateLibrary_maj_all h _) (fun d _ => templateLibrary_maj_all h _)
    (translate_hops h consts N mode nat power recipes rH fun i hi => (hπ i hi).2)).mono
    (recipeHeight_translate_le consts N mode nat power rH fun i hi => (hπ i hi).1) hB1

end ZInQ.Size

/-! ### The seven recipes of the specification -/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax ZInQ.Compiler.Natural

variable {E : Type} {B : ℕ} {I : Constructors E} {cstar ell T c3 : ℤ} {N : NatCircuit}

theorem le_of_two_pow_twenty_le {n : ℕ} (hB : 2 ^ 20 ≤ B) (hn : n ≤ 2 ^ 20) : n ≤ B :=
  hn.trans hB

/-- The callee of a composition call of recipe `i`: a template, or a recipe before `i`. -/
theorem callTarget_maj (h : LibraryAdmissible B I cstar ell T c3) {i : ℕ} (hi : i ≤ 7)
    {rH : List ℕ} (hrH : ∀ j < i, Maj B (rH.getD j 0) (getEx (specLib I cstar ell T c3 N) j).poly)
    (t : CallTarget) (ht : ∀ j, t = .recipe j → j < i) :
    Maj B (callTargetHeight templateHeightTable rH t)
      (t.resolve (templateLibrary I cstar ell T c3)
        (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take i))).poly := by
  cases t with
  | template k => exact templateLibrary_maj_all h k
  | recipe j =>
    have hj := ht j rfl
    show Maj B (rH.getD j 0)
      (getEx (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take i)) j).poly
    rw [getEx_specLib_take I cstar ell T c3 N hj hi]
    exact hrH j hj

/-- A composition recipe of the specification satisfies the majorant at its recipe height. -/
theorem specLib_composition_maj (h : LibraryAdmissible B I cstar ell T c3) {i : ℕ} (hi : i < 7)
    {r : CompositionRecipe}
    (hr : getEx (specLib I cstar ell T c3 N) i = (Recipe.composition r).denote
      (templateLibrary I cstar ell T c3)
      (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take i)))
    {rH : List ℕ} (hrH : ∀ j < i, Maj B (rH.getD j 0) (getEx (specLib I cstar ell T c3 N) j).poly)
    (hlen : r.calls.length ≤ 2 ^ 20) (hrec : ∀ c ∈ r.calls, ∀ j, c.target = .recipe j → j < i)
    {H : ℕ} (hH : recipeHeight templateHeightTable rH (.composition r) ≤ H) :
    Maj B H (getEx (specLib I cstar ell T c3 N) i).poly := by
  rw [hr]
  exact (composition_majorant h.two_pow_le _ _ templateHeightTable rH r
    (le_of_two_pow_twenty_le h.two_pow_le hlen)
    (fun c hc => callTarget_maj h hi.le hrH c.target (hrec c hc))).mono hH
    (one_le_of_two_pow_twenty_le h.two_pow_le)

theorem powerValue_maj (h : LibraryAdmissible B I cstar ell T c3) :
    Maj B 228 (getEx (specLib I cstar ell T c3 N) 0).poly := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  have := translate_majorant (Hπ := 0) h powerConstants powerTemplateCircuit .value false none
    (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take 0)) []
    (fun i hi => by simp at hi)
    (le_of_two_pow_twenty_le h.two_pow_le
      (by rw [← powerValueRecipe, powerValueRecipe_conjuncts_length]; norm_num))
  exact this

theorem precision_maj (h : LibraryAdmissible B I cstar ell T c3) (hN : PrecisionShape N c3) :
    Maj B 233 (getEx (specLib I cstar ell T c3 N) 1).poly := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  have := translate_majorant (Hπ := 228) h (integerConstants c3) N .zero true
    (some (0, powerValueRecipe.variableCount - powerValueRecipe.parameterCount))
    (denoteRecipes (templateLibrary I cstar ell T c3) ((specRecipes N c3).take 1)) [228]
    (fun i hi => by
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      refine ⟨le_rfl, ?_⟩
      rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
      exact powerValue_maj h)
    (le_of_two_pow_twenty_le h.two_pow_le
      ((precisionRecipe_conjuncts_length_le hN _ _).trans (by norm_num)))
  exact this

theorem close_maj (h : LibraryAdmissible B I cstar ell T c3) (hN : PrecisionShape N c3) :
    Maj B 235 (getEx (specLib I cstar ell T c3 N) 2).poly := by
  refine specLib_composition_maj (rH := [228, 233]) h (by decide) (getEx_specLib I cstar ell T c3 N (by decide)) ?_
    (by rw [closeRecipe_calls]; simp) (by simp [closeRecipe_calls])
    (Nat.le_of_ble_eq_true rfl)
  intro j hj
  interval_cases j
  · exact powerValue_maj h
  · exact precision_maj h hN

theorem main_maj (h : LibraryAdmissible B I cstar ell T c3) (hN : PrecisionShape N c3) :
    Maj B 251 (getEx (specLib I cstar ell T c3 N) 3).poly := by
  refine specLib_composition_maj (rH := [228, 233, 235]) h (by decide) (getEx_specLib I cstar ell T c3 N (by decide)) ?_
    (by rw [mainRecipe_calls]; simp) (by simp [mainRecipe_calls])
    (Nat.le_of_ble_eq_true rfl)
  intro j hj
  interval_cases j
  · exact powerValue_maj h
  · exact precision_maj h hN
  · exact close_maj h hN

theorem valueUnion_maj (h : LibraryAdmissible B I cstar ell T c3) (hN : PrecisionShape N c3) :
    Maj B 252 (getEx (specLib I cstar ell T c3 N) 4).poly := by
  refine specLib_composition_maj (rH := [228, 233, 235, 251]) h (by decide) (getEx_specLib I cstar ell T c3 N (by decide)) ?_
    (by rw [valueUnionRecipe_calls]; simp) (by simp [valueUnionRecipe_calls])
    (Nat.le_of_ble_eq_true rfl)
  intro j hj
  interval_cases j
  · exact powerValue_maj h
  · exact precision_maj h hN
  · exact close_maj h hN
  · exact main_maj h hN

theorem value_maj (h : LibraryAdmissible B I cstar ell T c3) (hN : PrecisionShape N c3) :
    Maj B 254 (getEx (specLib I cstar ell T c3 N) 5).poly := by
  refine specLib_composition_maj (rH := [228, 233, 235, 251, 252]) h (by decide) (getEx_specLib I cstar ell T c3 N (by decide)) ?_
    (by rw [valueRecipe_calls]; simp) (by simp [valueRecipe_calls])
    (Nat.le_of_ble_eq_true rfl)
  intro j hj
  interval_cases j
  · exact powerValue_maj h
  · exact precision_maj h hN
  · exact close_maj h hN
  · exact main_maj h hN
  · exact valueUnion_maj h hN

theorem integers_maj (h : LibraryAdmissible B I cstar ell T c3) (hN : PrecisionShape N c3) :
    Maj B 256 (getEx (specLib I cstar ell T c3 N) 6).poly := by
  refine specLib_composition_maj (rH := [228, 233, 235, 251, 252, 254]) h (by decide) (getEx_specLib I cstar ell T c3 N (by decide)) ?_
    (by rw [integersRecipe_calls]; simp) (by simp [integersRecipe_calls])
    (Nat.le_of_ble_eq_true rfl)
  intro j hj
  interval_cases j
  · exact powerValue_maj h
  · exact precision_maj h hN
  · exact close_maj h hN
  · exact main_maj h hN
  · exact valueUnion_maj h hN
  · exact value_maj h hN

/-- **Recipe heights.** For an admissible bound `B` and a natural precision circuit of the shape
of the compiler chapter, the recipes `power_value`, `precision`, `close`, `main`,
`value_union`, `value` and `integers` satisfy the majorant at the heights
`228, 233, 235, 251, 252, 254, 256`. -/
theorem recipe_heights (h : LibraryAdmissible B I cstar ell T c3) (hN : PrecisionShape N c3) :
    Maj B 228 (getEx (specLib I cstar ell T c3 N) 0).poly ∧
      Maj B 233 (getEx (specLib I cstar ell T c3 N) 1).poly ∧
      Maj B 235 (getEx (specLib I cstar ell T c3 N) 2).poly ∧
      Maj B 251 (getEx (specLib I cstar ell T c3 N) 3).poly ∧
      Maj B 252 (getEx (specLib I cstar ell T c3 N) 4).poly ∧
      Maj B 254 (getEx (specLib I cstar ell T c3 N) 5).poly ∧
      Maj B 256 (getEx (specLib I cstar ell T c3 N) 6).poly :=
  ⟨powerValue_maj h, precision_maj h hN, close_maj h hN, main_maj h hN, valueUnion_maj h hN,
    value_maj h hN, integers_maj h hN⟩

end ZInQ.Size
