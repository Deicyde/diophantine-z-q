import ZInQKernel.Syntax.Builder.Scope
import ZInQKernel.Assembly.Values.Outer
import ZInQKernel.Compiler.Translation.TranslateSemantics
import ZInQKernel.Compiler.Translation.Rational

/-!
# Witness scope of the recipes

Blueprint: `syntax/language/builder-well-formed.md` (recipes).

* Composition recipes (`CompositionRecipe.witnessScope_of`): if the arguments of the calls lie
  below a bound `B` at or above the parameter count, every call starts at or above `B`, and the
  call blocks `[w, w + m)` (`m` the witness count of the callee) are pairwise disjoint, the recipe
  is in scope. For the five composition recipes of the specification the blocks are allocated
  one after the other by the counter of `CompM`, above the parameters and the fresh ranges; their
  disjointness is `closeRecipe_callBlocks_disjoint`, …, `integersRecipe_callBlocks_disjoint`
  (`ZInQKernel/Syntax/Recipes/Outer.lean`, where the relations of `Assembly/Values/Outer.lean`
  also use them), and their witness scope `closeRecipe_witnessScope`, …, `integersRecipe_witnessScope`, for every
  template library and list of earlier recipes with the right witness counts.
* Model-evaluation recipes (`translate_witnessScope`): the translation of a well-formed natural
  circuit is in scope (`ZInQ.Translation.translate_scopedIn`, with the upper end of the blocks
  from the allocation invariant of the translation).
* The specification (`specLib_witnessScope`): every recipe of the specification is in scope,
  given that the precision circuit is well formed and its nontrivial constants are in the
  constant table; for the natural precision circuit of the compiler chapter
  (`specLib_precisionCircuit_witnessScope`) unconditionally.
-/

namespace ZInQ.Syntax

open MvPolynomial
open ZInQ.Compiler.Natural (NatCircuit NatNode)

/-! ### Composition recipes -/

/-- **Witness scope of a composition recipe.** If the arguments of the calls lie below `B`, the
calls start at or above `B ≥ p`, and the call blocks are pairwise disjoint, then the formula of
the recipe is in scope. -/
theorem CompositionRecipe.inScope_of {T R : List ExPoly} {r : CompositionRecipe}
    (hr : r.InRange T R) {B : ℕ} (hp : r.parameterCount ≤ B)
    (hargs : ∀ c ∈ r.calls, ∀ j ∈ c.args, j < B) (hstart : ∀ c ∈ r.calls, B ≤ c.start)
    (hdisj : (r.callBlocks T R).Pairwise BlockDisjoint) :
    (r.formula T R).InScope r.parameterCount r.variableCount := by
  obtain ⟨hbl, hca, hfr⟩ := Assembly.compositionRecipe_formula_parts T R r
  have hvars : VarsLT (r.formula T R).compile r.variableCount := by
    have := CompositionRecipe.varsLT_poly hr
    rwa [Recipe.poly_eq_compile] at this
  exact
    { scopedIn :=
        { scope :=
            { wf := fun τ hτ => by
                rw [hca] at hτ
                obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hτ
                exact (hr.calls c hc).1
              disjoint := hbl ▸ hdisj
              free := fun f hf i hi hb => by
                obtain ⟨c, hc, hic⟩ := hfr f hf i hi
                have := hargs c hc i hic
                rw [hbl] at hb
                obtain ⟨b, hb, hib⟩ := hb
                obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hb
                have := hstart c' hc'
                exact absurd hib.1 (by omega) }
          above := fun b hb => by
            rw [hbl] at hb
            obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
            exact hp.trans (hstart c hc)
          varsLT := hvars
          le := hr.params_le }
      inside := fun b hb => by
        rw [hbl] at hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact (hr.calls c hc).2.2 }

theorem Recipe.denote_varCount (T R : List ExPoly) (ρ : Recipe)
    (h : ρ.parameterCount ≤ ρ.variableCount) : (ρ.denote T R).varCount = ρ.variableCount :=
  Nat.add_sub_cancel' h

theorem CompositionRecipe.witnessScope_of {T R : List ExPoly} {r : CompositionRecipe}
    (hr : r.InRange T R) {B : ℕ} (hp : r.parameterCount ≤ B)
    (hargs : ∀ c ∈ r.calls, ∀ j ∈ c.args, j < B) (hstart : ∀ c ∈ r.calls, B ≤ c.start)
    (hdisj : (r.callBlocks T R).Pairwise BlockDisjoint) :
    ((Recipe.composition r).denote T R).WitnessScope := by
  refine ⟨r.formula T R, Recipe.poly_eq_compile T R (.composition r), ?_⟩
  rw [Recipe.denote_varCount T R (.composition r) hr.params_le]
  exact CompositionRecipe.inScope_of hr hp hargs hstart hdisj

/-! ### The composition recipes of the specification -/

section Compositions

variable (T R : List ExPoly)

/-- **Witness scope of `close`.** -/
theorem closeRecipe_witnessScope (w : ℕ) (h13 : (getEx T 13).WF)
    (h13w : (getEx T 13).witnesses = 140654) (h15 : (getEx T 15).WF)
    (h15w : (getEx T 15).witnesses = 53) (h1 : (getEx R 1).WF)
    (h1w : (getEx R 1).witnesses = w) :
    ((Recipe.composition (closeRecipe w)).denote T R).WitnessScope := by
  refine CompositionRecipe.witnessScope_of (closeRecipe_inRange T R w h13 h13w h15 h15w h1 h1w)
    (B := 51) (by rw [closeRecipe_parameterCount]; omega) ?_ ?_
    (closeRecipe_callBlocks_disjoint T R w h13w h15w h1w)
  · rw [closeRecipe_calls]
    intro c hc j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega
  · rw [closeRecipe_calls]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- **Witness scope of `main`.** -/
theorem mainRecipe_witnessScope (w : ℕ) (h16 : (getEx T 16).WF)
    (h16w : (getEx T 16).witnesses = 35282) (h2 : (getEx R 2).WF)
    (h2w : (getEx R 2).witnesses = w) :
    ((Recipe.composition (mainRecipe w)).denote T R).WitnessScope := by
  refine CompositionRecipe.witnessScope_of (mainRecipe_inRange T R w h16 h16w h2 h2w)
    (B := 11) (by rw [mainRecipe_parameterCount]; omega) ?_ ?_
    (mainRecipe_callBlocks_disjoint T R w h16w h2w)
  · rw [mainRecipe_calls]
    intro c hc j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega
  · rw [mainRecipe_calls]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp only <;> omega

/-- **Witness scope of `value_union`.** -/
theorem valueUnionRecipe_witnessScope (w : ℕ) (h17 : (getEx T 17).WF)
    (h17w : (getEx T 17).witnesses = 406) (h3 : (getEx R 3).WF)
    (h3w : (getEx R 3).witnesses = w) :
    ((Recipe.composition (valueUnionRecipe w)).denote T R).WitnessScope := by
  refine CompositionRecipe.witnessScope_of (valueUnionRecipe_inRange T R w h17 h17w h3 h3w)
    (B := 6) (by rw [valueUnionRecipe_parameterCount]) ?_ ?_
    (valueUnionRecipe_callBlocks_disjoint T R w h17w h3w)
  · rw [valueUnionRecipe_calls]
    intro c hc j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega
  · rw [valueUnionRecipe_calls]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp only <;> omega

/-- **Witness scope of `value`.** -/
theorem valueRecipe_witnessScope (w : ℕ) (h0 : (getEx T 0).WF)
    (h0w : (getEx T 0).witnesses = 7) (h4 : (getEx R 4).WF)
    (h4w : (getEx R 4).witnesses = w) :
    ((Recipe.composition (valueRecipe w)).denote T R).WitnessScope := by
  refine CompositionRecipe.witnessScope_of (valueRecipe_inRange T R w h0 h0w h4 h4w)
    (B := 6) (by rw [valueRecipe_parameterCount]) ?_ ?_
    (valueRecipe_callBlocks_disjoint T R w h0w h4w)
  · rw [valueRecipe_calls]
    intro c hc j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega
  · rw [valueRecipe_calls]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp only <;> omega

/-- **Witness scope of `integers`.** -/
theorem integersRecipe_witnessScope (w : ℕ) (h5 : (getEx R 5).WF)
    (h5w : (getEx R 5).witnesses = w) :
    ((Recipe.composition (integersRecipe w)).denote T R).WitnessScope := by
  refine CompositionRecipe.witnessScope_of (integersRecipe_inRange T R w h5 h5w)
    (B := 6) (by rw [integersRecipe_parameterCount]; omega) ?_ ?_
    (integersRecipe_callBlocks_disjoint T R w)
  · rw [integersRecipe_calls]
    intro c hc j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    simp only [List.mem_append, mem_point, List.mem_singleton] at hj
    omega
  · rw [integersRecipe_calls]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    simp only
    omega

end Compositions

/-! ### Model-evaluation recipes -/

theorem ModelRecipe.witnessScope_of {T R : List ExPoly} {r : ModelRecipe}
    (h : Translation.ScopedIn (r.formula T R) r.parameterCount r.variableCount)
    (hin : ∀ b ∈ (r.formula T R).blocks, b.1 + b.2 ≤ r.variableCount) :
    ((Recipe.model r).denote T R).WitnessScope := by
  refine ⟨r.formula T R, Recipe.poly_eq_compile T R (.model r), ?_⟩
  rw [Recipe.denote_varCount T R (.model r) h.le]
  exact ⟨h, hin⟩

section Translate

variable {consts : List ℤ} {N P : NatCircuit} {V : ℕ} {mode : OutputMode} {natIn : Bool}
  {power : Option (ℕ × ℕ)}

/-- The call blocks of a translation end at or below its variable count. -/
theorem translate_blocks_end_le (hwf : Translation.WellFormed P N V)
    {templates recipes : List ExPoly}
    (hνw : (getEx templates 12).witnesses = 140604) (hαw : (getEx templates 1).witnesses = 6)
    (hμw : (getEx templates 11).witnesses = 35134)
    (hcw : ∀ c, NatNode.const c ∈ N.nodes → Translation.Nontrivial c →
      (getEx templates (18 + consts.idxOf c)).witnesses = 1)
    (hpw : ∀ i w, power = some (i, w) → (getEx recipes i).witnesses = w) :
    ∀ b ∈ ((translate consts N mode natIn power).formula templates recipes).blocks,
      b.1 + b.2 ≤ (translate consts N mode natIn power).variableCount := by
  have hN := Translation.trRun_nodeInv consts N mode natIn power hwf.core.args_lt
  have hbl := Translation.blocks_translate (mode := mode) (natIn := natIn) hwf hνw hαw hμw hcw hpw
  intro b hb
  rw [hbl] at hb
  rw [Translation.translate_variableCount_eq]
  exact (hN.alloc.block_range b (hN.perm.subset hb)).2

/-- **Witness scope of the model-evaluation translation** of a well-formed circuit. -/
theorem translate_witnessScope (hwf : Translation.WellFormed P N V)
    {templates recipes : List ExPoly} (ht : ∀ τ ∈ templates, τ.WF)
    (hr : ∀ i w, power = some (i, w) → (getEx recipes i).WF)
    (hνw : (getEx templates 12).witnesses = 140604) (hαw : (getEx templates 1).witnesses = 6)
    (hμw : (getEx templates 11).witnesses = 35134)
    (hcw : ∀ c, NatNode.const c ∈ N.nodes → Translation.Nontrivial c →
      (getEx templates (18 + consts.idxOf c)).witnesses = 1)
    (hpw : ∀ i w, power = some (i, w) → (getEx recipes i).witnesses = w) :
    ((Recipe.model (translate consts N mode natIn power)).denote templates recipes).WitnessScope :=
  ModelRecipe.witnessScope_of (Translation.translate_scopedIn hwf ht hr hνw hαw hμw hcw hpw)
    (translate_blocks_end_le hwf hνw hαw hμw hcw hpw)

/-- The translation with the template library: the constant table is a prefix of
`(4, 2, 3, c₃, 1399)` containing the nontrivial constants of the circuit, and the power recipe,
if any, is well formed with the recorded witness count. -/
theorem translate_witnessScope_library {E : Type} (I : Constructors E) (cstar ell T c3 : ℤ)
    (hwf : Translation.WellFormed P N V) (hcons : consts <+: integerConstants c3)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Translation.Nontrivial c → c ∈ consts)
    {recipes : List ExPoly} (hr : ∀ i w, power = some (i, w) → (getEx recipes i).WF)
    (hpw : ∀ i w, power = some (i, w) → (getEx recipes i).witnesses = w) :
    ((Recipe.model (translate consts N mode natIn power)).denote
      (templateLibrary I cstar ell T c3) recipes).WitnessScope := by
  obtain ⟨h1, h2, h3⟩ := Translation.library_witnesses I cstar ell T c3
  refine translate_witnessScope hwf (templateLibrary_wf I cstar ell T c3) hr h1 h2 h3
    (fun c hc hn => ?_) hpw
  rw [Translation.getEx_library_scalar I cstar ell T c3 hcons (hcmem c hc hn),
    scalarTemplate_witnesses]

end Translate

/-! ### The specification -/

section Spec

variable {E : Type} (I : Constructors E) (cstar ell T c3 : ℤ) (N : NatCircuit)

theorem specLib_witnessScope_0 : (getEx (specLib I cstar ell T c3 N) 0).WitnessScope := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  exact translate_witnessScope_library I cstar ell T c3 Translation.powerTemplate_wellFormed.1
    (Translation.powerConstants_prefix c3) Translation.powerTemplate_consts
    (fun i w h => by cases h) (fun i w h => by cases h)

theorem specLib_witnessScope_1 {P : NatCircuit} {V : ℕ} (hwf : Translation.WellFormed P N V)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Translation.Nontrivial c →
      c ∈ integerConstants c3) :
    (getEx (specLib I cstar ell T c3 N) 1).WitnessScope := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine translate_witnessScope_library I cstar ell T c3 hwf (List.prefix_refl _) hcmem ?_ ?_
  · intro i w h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_0 I cstar ell T c3 N
  · intro i w h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_witnessScope_2 : (getEx (specLib I cstar ell T c3 N) 2).WitnessScope := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine closeRecipe_witnessScope _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 13) (by rw [templateLibrary_getEx_witnesses]; rfl)
    (templateLibrary_getEx_wf I cstar ell T c3 15) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_1 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_witnessScope_3 : (getEx (specLib I cstar ell T c3 N) 3).WitnessScope := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine mainRecipe_witnessScope _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 16) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_2 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_witnessScope_4 : (getEx (specLib I cstar ell T c3 N) 4).WitnessScope := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine valueUnionRecipe_witnessScope _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 17) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_3 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_witnessScope_5 : (getEx (specLib I cstar ell T c3 N) 5).WitnessScope := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine valueRecipe_witnessScope _ _ _
    (templateLibrary_getEx_wf I cstar ell T c3 0) (by rw [templateLibrary_getEx_witnesses]; rfl)
    ?_ ?_
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_4 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

theorem specLib_witnessScope_6 : (getEx (specLib I cstar ell T c3 N) 6).WitnessScope := by
  rw [getEx_specLib I cstar ell T c3 N (by decide)]
  refine integersRecipe_witnessScope _ _ _ ?_ ?_
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
    exact specLib_wf_5 I cstar ell T c3 N
  · rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide),
      getEx_specLib_witnesses I cstar ell T c3 N (by decide)]
    rfl

/-- **Witness scope of the specified recipes.** If the precision circuit is well formed and its
nontrivial constants are among `(4, 2, 3, c₃, 1399)`, every recipe of the specification is in
scope. -/
theorem specLib_witnessScope {P : NatCircuit} {V : ℕ} (hwf : Translation.WellFormed P N V)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Translation.Nontrivial c →
      c ∈ integerConstants c3) :
    ∀ τ ∈ specLib I cstar ell T c3 N, τ.WitnessScope := by
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
  · exact specLib_witnessScope_0 I cstar ell T c3 N
  · exact specLib_witnessScope_1 I cstar ell T c3 N hwf hcmem
  · exact specLib_witnessScope_2 I cstar ell T c3 N
  · exact specLib_witnessScope_3 I cstar ell T c3 N
  · exact specLib_witnessScope_4 I cstar ell T c3 N
  · exact specLib_witnessScope_5 I cstar ell T c3 N
  · exact specLib_witnessScope_6 I cstar ell T c3 N

end Spec

/-- The nontrivial constants of the natural precision circuit are among `(4, 2, 3, c₃, 1399)`. -/
theorem precisionCircuit_consts_mem_integerConstants :
    ∀ c, NatNode.const c ∈ Compiler.Universal.precisionCircuit.nodes →
      Translation.Nontrivial c → c ∈ integerConstants (Compiler.Universal.c3 : ℤ) := by
  intro c hc hn
  have := Compiler.Universal.precisionCircuitOf_consts (Compiler.Universal.c3 : ℤ) hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  obtain ⟨h0, h1, h2⟩ := hn
  simp only [integerConstants, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **Witness scope of the specification** at the natural precision circuit of the compiler
chapter: every template of the library and every recipe of the specification is in scope. -/
theorem specLib_precisionCircuit_witnessScope {E : Type} (I : Constructors E) (cstar ell T : ℤ) :
    (∀ τ ∈ templateLibrary I cstar ell T (Compiler.Universal.c3 : ℤ), τ.WitnessScope) ∧
      ∀ τ ∈ specLib I cstar ell T (Compiler.Universal.c3 : ℤ) Compiler.Universal.precisionCircuit,
        τ.WitnessScope :=
  ⟨templateLibrary_witnessScope I cstar ell T _,
    specLib_witnessScope I cstar ell T _ _ Translation.precisionCircuit_wellFormed.1
      precisionCircuit_consts_mem_integerConstants⟩

end ZInQ.Syntax
