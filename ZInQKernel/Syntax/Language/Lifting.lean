import ZInQKernel.Syntax.Language.Formula

/-!
# Private witness blocks

Every call atom `⟨τ[g; w]⟩` of a formula owns the block `[w, w + m)` of the caller's
variables, where `m` is the witness count of `τ`. If the blocks are pairwise disjoint and no
block variable occurs in a parameter polynomial or in an atom `a ≐ b`, `⟨f⟩`, then the
compiled formula has a zero after choosing the block variables exactly when the formula
holds with every call atom replaced by the callee relation (`Formula.exists_blocks_iff`).
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- `i` lies in the block `b = (start, length)`. -/
def InBlock (b : ℕ × ℕ) (i : ℕ) : Prop := b.1 ≤ i ∧ i < b.1 + b.2

/-- `i` lies in one of the blocks of `l`. -/
def InBlocks (l : List (ℕ × ℕ)) (i : ℕ) : Prop := ∃ b ∈ l, InBlock b i

/-- Two blocks are disjoint. -/
def BlockDisjoint (b b' : ℕ × ℕ) : Prop := ∀ i, InBlock b i → ¬ InBlock b' i

instance : Std.Symm BlockDisjoint := ⟨fun _ _ h i h' h'' => h i h'' h'⟩

theorem inBlocks_flatMap {α : Type*} {l : List α} {f : α → List (ℕ × ℕ)} {i : ℕ} :
    InBlocks (l.flatMap f) i ↔ ∃ a ∈ l, InBlocks (f a) i := by
  simp only [InBlocks, List.mem_flatMap]
  exact ⟨fun ⟨b, ⟨a, ha, hb⟩, hi⟩ => ⟨a, ha, b, hb, hi⟩,
    fun ⟨a, ha, b, hb, hi⟩ => ⟨b, ⟨a, ha, hb⟩, hi⟩⟩

namespace Formula

/-- The witness blocks `(w, m)` of the call atoms. -/
def blocks : Formula → List (ℕ × ℕ)
  | .eq _ _ => []
  | .atom _ => []
  | .call τ _ w => [(w, τ.witnesses)]
  | .and fs => fs.flatMap fun φ => φ.blocks
  | .or fs => fs.flatMap fun φ => φ.blocks

/-- The polynomials that must avoid the blocks: the parameter polynomials of the calls and
the polynomials of the atoms `a ≐ b` and `⟨f⟩`. -/
def freePolys : Formula → List Poly
  | .eq a b => [a, b]
  | .atom f => [f]
  | .call _ g _ => List.ofFn g
  | .and fs => fs.flatMap fun φ => φ.freePolys
  | .or fs => fs.flatMap fun φ => φ.freePolys

/-- The callees of the call atoms. -/
def callees : Formula → List ExPoly
  | .eq _ _ => []
  | .atom _ => []
  | .call τ _ _ => [τ]
  | .and fs => fs.flatMap fun φ => φ.callees
  | .or fs => fs.flatMap fun φ => φ.callees

/-- `φ^*(x)`: the formula with every call atom replaced by the callee relation at the values
of its parameter polynomials. -/
def Lift (x : ℕ → ℚ) : Formula → Prop
  | .eq a b => ev x a = ev x b
  | .atom f => ev x f = 0
  | .call τ g _ => τ.Rel fun k => ev x (g k)
  | .and fs => ∀ φ, (_ : φ ∈ fs) → Lift x φ
  | .or fs => ∃ φ, ∃ (_ : φ ∈ fs), Lift x φ
decreasing_by all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ fs›; simp; omega)

@[simp] theorem blocks_and (fs : List Formula) : (Formula.and fs).blocks = fs.flatMap blocks := by
  rw [blocks]

@[simp] theorem blocks_or (fs : List Formula) : (Formula.or fs).blocks = fs.flatMap blocks := by
  rw [blocks]

@[simp] theorem freePolys_and (fs : List Formula) :
    (Formula.and fs).freePolys = fs.flatMap freePolys := by rw [freePolys]

@[simp] theorem freePolys_or (fs : List Formula) :
    (Formula.or fs).freePolys = fs.flatMap freePolys := by rw [freePolys]

@[simp] theorem callees_and (fs : List Formula) :
    (Formula.and fs).callees = fs.flatMap callees := by rw [callees]

@[simp] theorem callees_or (fs : List Formula) :
    (Formula.or fs).callees = fs.flatMap callees := by rw [callees]

@[simp] theorem lift_eq (x : ℕ → ℚ) (a b : Poly) :
    (Formula.eq a b).Lift x ↔ ev x a = ev x b := by simp [Lift]

@[simp] theorem lift_atom (x : ℕ → ℚ) (f : Poly) : (Formula.atom f).Lift x ↔ ev x f = 0 := by
  simp [Lift]

@[simp] theorem lift_call (x : ℕ → ℚ) (τ : ExPoly) (g : Fin τ.params → Poly) (w : ℕ) :
    (Formula.call τ g w).Lift x ↔ τ.Rel fun k => ev x (g k) := by simp [Lift]

@[simp] theorem lift_and (x : ℕ → ℚ) (fs : List Formula) :
    (Formula.and fs).Lift x ↔ ∀ φ ∈ fs, φ.Lift x := by rw [Lift]

@[simp] theorem lift_or (x : ℕ → ℚ) (fs : List Formula) :
    (Formula.or fs).Lift x ↔ ∃ φ ∈ fs, φ.Lift x := by
  rw [Lift]
  exact ⟨fun ⟨φ, hφ, h⟩ => ⟨φ, hφ, h⟩, fun ⟨φ, hφ, h⟩ => ⟨φ, hφ, h⟩⟩

theorem mem_vars_list_sum {l : List Poly} {i : ℕ} (h : i ∈ l.sum.vars) : ∃ f ∈ l, i ∈ f.vars := by
  classical
  induction l with
  | nil => simp at h
  | cons f l ih =>
    rw [List.sum_cons] at h
    rcases Finset.mem_union.1 (vars_add_subset _ _ h) with h | h
    · exact ⟨f, List.mem_cons_self, h⟩
    · obtain ⟨g, hg, hi⟩ := ih h
      exact ⟨g, List.mem_cons_of_mem _ hg, hi⟩

theorem mem_vars_list_prod {l : List Poly} {i : ℕ} (h : i ∈ l.prod.vars) :
    ∃ f ∈ l, i ∈ f.vars := by
  classical
  induction l with
  | nil => simp at h
  | cons f l ih =>
    rw [List.prod_cons] at h
    rcases Finset.mem_union.1 (vars_mul _ _ h) with h | h
    · exact ⟨f, List.mem_cons_self, h⟩
    · obtain ⟨g, hg, hi⟩ := ih h
      exact ⟨g, List.mem_cons_of_mem _ hg, hi⟩

/-- A variable of a compiled formula occurs in a free polynomial or lies in a block. -/
theorem mem_vars_compile {φ : Formula} (hwf : ∀ τ ∈ φ.callees, τ.WF) {i : ℕ}
    (hi : i ∈ φ.compile.vars) : (∃ f ∈ φ.freePolys, i ∈ f.vars) ∨ InBlocks φ.blocks i := by
  classical
  induction φ using Formula.induct' with
  | eq a b =>
    rw [compile_eq] at hi
    rcases Finset.mem_union.1 (vars_sub_subset (p := a) (q := b) hi) with h | h
    · exact Or.inl ⟨a, by simp [freePolys], h⟩
    · exact Or.inl ⟨b, by simp [freePolys], h⟩
  | atom f => exact Or.inl ⟨f, by simp [freePolys], by simpa using hi⟩
  | call τ g w =>
    rw [compile_call] at hi
    rcases mem_vars_callPoly (hwf τ (by simp [callees])) g hi with ⟨k, hk⟩ | h
    · exact Or.inl ⟨g k, by simp [freePolys], hk⟩
    · exact Or.inr ⟨(w, τ.witnesses), by simp [blocks], h⟩
  | and fs ih =>
    rw [compile_and] at hi
    obtain ⟨f, hf, hif⟩ := mem_vars_list_sum hi
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
    have hwf' : ∀ τ ∈ φ.callees, τ.WF := fun τ hτ =>
      hwf τ (by rw [callees_and]; exact List.mem_flatMap.2 ⟨φ, hφ, hτ⟩)
    rcases ih φ hφ hwf' (vars_pow _ _ hif) with ⟨f, hf, h⟩ | h
    · exact Or.inl ⟨f, by rw [freePolys_and]; exact List.mem_flatMap.2 ⟨φ, hφ, hf⟩, h⟩
    · exact Or.inr (by rw [blocks_and]; exact inBlocks_flatMap.2 ⟨φ, hφ, h⟩)
  | or fs ih =>
    rw [compile_or] at hi
    obtain ⟨f, hf, hif⟩ := mem_vars_list_prod hi
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
    have hwf' : ∀ τ ∈ φ.callees, τ.WF := fun τ hτ =>
      hwf τ (by rw [callees_or]; exact List.mem_flatMap.2 ⟨φ, hφ, hτ⟩)
    rcases ih φ hφ hwf' hif with ⟨f, hf, h⟩ | h
    · exact Or.inl ⟨f, by rw [freePolys_or]; exact List.mem_flatMap.2 ⟨φ, hφ, hf⟩, h⟩
    · exact Or.inr (by rw [blocks_or]; exact inBlocks_flatMap.2 ⟨φ, hφ, h⟩)

/-- The scope hypotheses of a formula: callees well formed, blocks pairwise disjoint, free
polynomials avoiding the blocks. -/
structure Scoped (φ : Formula) : Prop where
  wf : ∀ τ ∈ φ.callees, τ.WF
  disjoint : φ.blocks.Pairwise BlockDisjoint
  free : ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, ¬ InBlocks φ.blocks i

/-- The scope hypotheses pass to the members of a conjunction or disjunction. -/
theorem Scoped.of_mem {fs : List Formula} {φ : Formula} (hφ : φ ∈ fs)
    (wf : ∀ τ ∈ fs.flatMap callees, τ.WF) (disjoint : (fs.flatMap blocks).Pairwise BlockDisjoint)
    (free : ∀ f ∈ fs.flatMap freePolys, ∀ i ∈ f.vars, ¬ InBlocks (fs.flatMap blocks) i) :
    φ.Scoped where
  wf τ hτ := wf τ (List.mem_flatMap.2 ⟨φ, hφ, hτ⟩)
  disjoint := (List.pairwise_flatMap.1 disjoint).1 φ hφ
  free f hf i hi hb := free f (List.mem_flatMap.2 ⟨φ, hφ, hf⟩) i hi (inBlocks_flatMap.2 ⟨φ, hφ, hb⟩)

/-- Changing `y` to `x` outside the blocks of `φ` does not change the truth of `φ` when `y`
agrees with `x` on the free variables. -/
theorem holds_restrict {φ : Formula} (hφ : φ.Scoped) {x y : ℕ → ℚ}
    (hy : ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, y i = x i) :
    letI := Classical.propDecidable
    φ.Holds (fun i => if InBlocks φ.blocks i then y i else x i) ↔ φ.Holds y := by
  refine holds_congr fun i hi => ?_
  split_ifs with h
  · rfl
  · rcases mem_vars_compile hφ.wf hi with ⟨f, hf, hif⟩ | h'
    · exact (hy f hf i hif).symm
    · exact absurd h' h

/-- The induction behind `exists_blocks_iff`, stated with `Holds`. -/
theorem exists_holds_iff (φ : Formula) (hφ : φ.Scoped) (x : ℕ → ℚ) :
    (∃ y : ℕ → ℚ, (∀ i, ¬ InBlocks φ.blocks i → y i = x i) ∧ φ.Holds y) ↔ φ.Lift x := by
  classical
  induction φ using Formula.induct' generalizing x with
  | eq a b =>
    simp only [blocks, InBlocks, List.not_mem_nil, false_and, exists_false, not_false_eq_true,
      forall_const, holds_eq, lift_eq]
    exact ⟨fun ⟨y, hy, h⟩ => (funext hy : y = x) ▸ h, fun h => ⟨x, fun _ => rfl, h⟩⟩
  | atom f =>
    simp only [blocks, InBlocks, List.not_mem_nil, false_and, exists_false, not_false_eq_true,
      forall_const, holds_atom, lift_atom]
    exact ⟨fun ⟨y, hy, h⟩ => (funext hy : y = x) ▸ h, fun h => ⟨x, fun _ => rfl, h⟩⟩
  | call τ g w =>
    have hτ : τ.WF := hφ.wf τ (by simp [callees])
    have hblock : ∀ i, InBlocks (Formula.call τ g w).blocks i ↔ w ≤ i ∧ i < w + τ.witnesses := by
      intro i; simp [blocks, InBlocks, InBlock]
    have hg : ∀ k, ∀ i ∈ (g k).vars, i < w ∨ w + τ.witnesses ≤ i := by
      intro k i hi
      have := hφ.free (g k) (by simp [freePolys]) i hi
      rw [hblock] at this
      omega
    rw [lift_call, ← ExPoly.exists_blockUpdate_call_iff hτ g w hg x]
    simp only [holds_call, hblock]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨fun j => y (w + j), ?_⟩
      rw [show blockUpdate x w τ.witnesses (fun j => y (w + j)) = y from funext fun i => ?_]
      · exact h
      unfold blockUpdate
      split_ifs with hi
      · show y (w + (i - w)) = y i
        rw [Nat.add_sub_cancel' hi.1]
      · exact (hy i (by omega)).symm
    · rintro ⟨y, h⟩
      exact ⟨_, fun i hi => blockUpdate_of_not_mem x w _ y (by omega), h⟩
  | and fs ih =>
    have hsub : ∀ φ ∈ fs, φ.Scoped := fun φ hφ' => by
      have := hφ; obtain ⟨h1, h2, h3⟩ := this
      simp only [callees_and, blocks_and, freePolys_and] at h1 h2 h3
      exact Scoped.of_mem hφ' h1 h2 h3
    have hfree : ∀ φ ∈ fs, ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, ¬ InBlocks (fs.flatMap blocks) i :=
      fun φ hφ' f hf i hi => by
        have := hφ.free f (by rw [freePolys_and]; exact List.mem_flatMap.2 ⟨φ, hφ', hf⟩) i hi
        rwa [blocks_and] at this
    simp only [blocks_and, holds_and, lift_and]
    constructor
    · rintro ⟨y, hy, h⟩ φ hφ'
      refine (ih φ hφ' (hsub φ hφ') x).1
        ⟨fun i => if InBlocks φ.blocks i then y i else x i, fun i hi => ?_, ?_⟩
      · simp only [hi, ite_false]
      · refine (holds_restrict (hsub φ hφ') fun f hf i hi => ?_).2 (h φ hφ')
        exact hy i (hfree φ hφ' f hf i hi)
    · intro h
      have hY : ∀ φ (hφ' : φ ∈ fs), ∃ y : ℕ → ℚ,
          (∀ i, ¬ InBlocks φ.blocks i → y i = x i) ∧ φ.Holds y :=
        fun φ hφ' => (ih φ hφ' (hsub φ hφ') x).2 (h φ hφ')
      choose Y hYx hYh using hY
      have hdisj := (List.pairwise_flatMap.1 (by simpa using hφ.disjoint)).2
      have : Std.Symm fun a b : Formula =>
          ∀ x ∈ a.blocks, ∀ y ∈ b.blocks, BlockDisjoint x y :=
        ⟨fun _ _ h x hx y hy => Std.Symm.symm _ _ (h y hy x hx)⟩
      -- The member of `fs` owning a block variable is unique.
      have huniq : ∀ φ ∈ fs, ∀ ψ ∈ fs, ∀ i, InBlocks φ.blocks i → InBlocks ψ.blocks i → φ = ψ := by
        intro φ hφ' ψ hψ i ⟨b, hb, hib⟩ ⟨b', hb', hib'⟩
        by_contra hne
        exact hdisj.forall hφ' hψ hne b hb b' hb' i hib hib'
      refine ⟨fun i => if hi : ∃ φ, ∃ (hφ' : φ ∈ fs), InBlocks φ.blocks i then
          Y hi.choose hi.choose_spec.choose i else x i, fun i hi => ?_, fun φ hφ' => ?_⟩
      · dsimp only
        rw [dite_eq_right ?_]
        rintro ⟨φ, hφ', hb⟩
        exact hi (inBlocks_flatMap.2 ⟨φ, hφ', hb⟩)
      · refine (holds_congr fun i hi => ?_).1 (hYh φ hφ')
        rcases mem_vars_compile (hsub φ hφ').wf hi with ⟨f, hf, hif⟩ | hb
        · have hnot := hfree φ hφ' f hf i hif
          rw [dite_eq_right ?_, hYx φ hφ' i]
          · intro hb; exact hnot (inBlocks_flatMap.2 ⟨φ, hφ', hb⟩)
          · rintro ⟨ψ, hψ, hb⟩; exact hnot (inBlocks_flatMap.2 ⟨ψ, hψ, hb⟩)
        · have hex : ∃ φ, ∃ (hφ' : φ ∈ fs), InBlocks φ.blocks i := ⟨φ, hφ', hb⟩
          rw [dite_eq_left hex]
          have heq : hex.choose = φ :=
            huniq _ hex.choose_spec.choose φ hφ' i hex.choose_spec.choose_spec hb
          have key : ∀ (ψ : Formula) (hψ : ψ ∈ fs), ψ = φ → Y φ hφ' i = Y ψ hψ i := by
            rintro ψ hψ rfl; rfl
          exact key _ _ heq
  | or fs ih =>
    have hsub : ∀ φ ∈ fs, φ.Scoped := fun φ hφ' => by
      have := hφ; obtain ⟨h1, h2, h3⟩ := this
      simp only [callees_or, blocks_or, freePolys_or] at h1 h2 h3
      exact Scoped.of_mem hφ' h1 h2 h3
    have hfree : ∀ φ ∈ fs, ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, ¬ InBlocks (fs.flatMap blocks) i :=
      fun φ hφ' f hf i hi => by
        have := hφ.free f (by rw [freePolys_or]; exact List.mem_flatMap.2 ⟨φ, hφ', hf⟩) i hi
        rwa [blocks_or] at this
    simp only [blocks_or, holds_or, lift_or]
    constructor
    · rintro ⟨y, hy, φ, hφ', h⟩
      refine ⟨φ, hφ', (ih φ hφ' (hsub φ hφ') x).1
        ⟨fun i => if InBlocks φ.blocks i then y i else x i, fun i hi => ?_, ?_⟩⟩
      · simp only [hi, ite_false]
      · refine (holds_restrict (hsub φ hφ') fun f hf i hi => ?_).2 h
        exact hy i (hfree φ hφ' f hf i hi)
    · rintro ⟨φ, hφ', h⟩
      obtain ⟨y, hy, hh⟩ := (ih φ hφ' (hsub φ hφ') x).2 h
      exact ⟨y, fun i hi => hy i fun hb => hi (inBlocks_flatMap.2 ⟨φ, hφ', hb⟩), φ, hφ', hh⟩

/-- **Private witness blocks.** Let the call blocks of `φ` be pairwise disjoint, let no block
variable occur in a parameter polynomial or in an atom `a ≐ b`, `⟨f⟩`, and let every callee
have its variables below its variable count. Then `κ(φ)` has a zero after choosing the block
variables exactly when `φ^*(x)` holds. -/
theorem exists_blocks_iff (φ : Formula) (hwf : ∀ τ ∈ φ.callees, τ.WF)
    (hdisj : φ.blocks.Pairwise BlockDisjoint)
    (hfree : ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, ¬ InBlocks φ.blocks i) (x : ℕ → ℚ) :
    (∃ y : ℕ → ℚ, (∀ i, ¬ InBlocks φ.blocks i → y i = x i) ∧ ev y φ.compile = 0) ↔ φ.Lift x := by
  simp only [ev_compile_eq_zero_iff]
  exact exists_holds_iff φ ⟨hwf, hdisj, hfree⟩ x

/-- `φ^*(x)` depends only on `x` outside the blocks. -/
theorem lift_congr {φ : Formula} (hφ : φ.Scoped) {x x' : ℕ → ℚ}
    (h : ∀ i, ¬ InBlocks φ.blocks i → x i = x' i) : φ.Lift x ↔ φ.Lift x' := by
  rw [← exists_holds_iff φ hφ, ← exists_holds_iff φ hφ]
  refine exists_congr fun y => and_congr_left fun _ => forall_congr' fun i => ?_
  exact imp_congr_right fun hi => by rw [h i hi]

end Formula

end ZInQ.Syntax
