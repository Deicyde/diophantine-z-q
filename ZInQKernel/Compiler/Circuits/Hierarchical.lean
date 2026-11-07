import ZInQKernel.Compiler.Circuits.Scope
import ZInQKernel.Compiler.Circuits.PowerTemplate
import ZInQKernel.Compiler.Circuits.Packed.Polynomial

/-!
# Circuits of hierarchical constructions

For a natural construction with `k` inputs whose node encoding is valid (`Triple`), its natural
circuit `𝒞` is well scoped (if the construction preserves the scope invariant), its variable
count is the final counter, and `[[𝒞]] = κ(φ)` (item 1). Item 2: if the call blocks of `φ` are
private (`Formula.Scoped`) and `κ(φ)` has its variables below the variable count, then
`Z_𝒞(c)` holds iff some natural values of the variables (equal to `c` on the inputs) satisfy
`φ^♮`, the formula with every call atom read through the natural relation of its template
(`NLift`); for the power template that relation is `P = Q^R` (`nlift_call_powerTemplate`).
Item 3 for the packed-history construction is `Packed.compiled_natRel_iff` (with
`Packed.packed_spec`, which lists the macro relations).

(Blueprint: `compiler/natural/formulas/hierarchical-calls.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- `φ^♮(x)`: the formula read at natural values, every call atom replaced by the natural
relation of its template at the values of its parameter polynomials. -/
def NLift (x : ℕ → ℕ) : Formula → Prop
  | .eq a b => zv x a = zv x b
  | .atom f => zv x f = 0
  | .call τ g _ => ExNatRel τ fun j => zv x (g j)
  | .and fs => ∀ φ, (_ : φ ∈ fs) → NLift x φ
  | .or fs => ∃ φ, ∃ (_ : φ ∈ fs), NLift x φ
decreasing_by all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ fs›; simp; omega)

@[simp] theorem nlift_eq (x : ℕ → ℕ) (a b : Poly) : NLift x (.eq a b) ↔ zv x a = zv x b := by
  simp [NLift]

@[simp] theorem nlift_atom (x : ℕ → ℕ) (f : Poly) : NLift x (.atom f) ↔ zv x f = 0 := by
  simp [NLift]

@[simp] theorem nlift_call (x : ℕ → ℕ) (τ : ExPoly) (g : Fin τ.params → Poly) (w : ℕ) :
    NLift x (.call τ g w) ↔ ExNatRel τ fun j => zv x (g j) := by simp [NLift]

@[simp] theorem nlift_and (x : ℕ → ℕ) (fs : List Formula) :
    NLift x (.and fs) ↔ ∀ φ ∈ fs, NLift x φ := by rw [NLift]

@[simp] theorem nlift_or (x : ℕ → ℕ) (fs : List Formula) :
    NLift x (.or fs) ↔ ∃ φ ∈ fs, NLift x φ := by
  rw [NLift]
  exact ⟨fun ⟨φ, hφ, h⟩ => ⟨φ, hφ, h⟩, fun ⟨φ, hφ, h⟩ => ⟨φ, hφ, h⟩⟩

/-- A call atom on a private block, over the naturals. -/
theorem exists_call_iff {τ : ExPoly} (hτ : τ.WF) (g : Fin τ.params → Poly) (w : ℕ)
    (hg : ∀ j, ∀ i ∈ (g j).vars, i < w ∨ w + τ.witnesses ≤ i) (x : ℕ → ℕ) :
    (∃ y : ℕ → ℕ, (∀ i, ¬ (w ≤ i ∧ i < w + τ.witnesses) → y i = x i) ∧
      zv y (τ.call g w) = 0) ↔ ExNatRel τ fun j => zv x (g j) := by
  have hgy : ∀ y : ℕ → ℕ, (∀ i, ¬ (w ≤ i ∧ i < w + τ.witnesses) → y i = x i) →
      ∀ j, zv y (g j) = zv x (g j) := fun y hy j =>
    zv_congr fun i hi => hy i (by have := hg j i hi; omega)
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨fun j => y (w + j), ?_⟩
    rw [← Int.cast_eq_zero (α := ℚ), ← ev_qa, ExPoly.ev_call hτ] at h
    rw [← h]
    refine congrArg (fun a => ev a τ.poly) (funext fun i => ?_)
    unfold assign
    split_ifs
    · simp only [← ev_qa]; rw [ev_qa, ev_qa, hgy y hy]
    · simp [qa]
    · rfl
  · rintro ⟨v, hv⟩
    let y : ℕ → ℕ := fun i =>
      if h : w ≤ i ∧ i - w < τ.witnesses then v ⟨i - w, h.2⟩ else x i
    have hy : ∀ i, ¬ (w ≤ i ∧ i < w + τ.witnesses) → y i = x i := fun i hi => by
      simp only [y]; rw [dite_eq_right]; rintro ⟨h1, h2⟩; exact hi ⟨h1, by omega⟩
    refine ⟨y, hy, ?_⟩
    rw [← Int.cast_eq_zero (α := ℚ), ← ev_qa, ExPoly.ev_call hτ, ← hv]
    refine congrArg (fun a => ev a τ.poly) (funext fun i => ?_)
    unfold assign
    split_ifs with h1 h2
    · show ev (qa y) (g ⟨i, h1⟩) = _
      rw [ev_qa, hgy y hy]
    · simp only [qa, y]
      rw [dite_eq_left ⟨by omega, by omega⟩]
      simp
    · rfl

theorem nholds_restrict {φ : Formula} (hφ : φ.Scoped) {x y : ℕ → ℕ}
    (hy : ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, y i = x i) :
    letI := Classical.propDecidable
    NHolds (fun i => if InBlocks φ.blocks i then y i else x i) φ ↔ NHolds y φ := by
  refine nholds_congr fun i hi => ?_
  split_ifs with h
  · rfl
  · rcases Formula.mem_vars_compile hφ.wf hi with ⟨f, hf, hif⟩ | h'
    · exact (hy f hf i hif).symm
    · exact absurd h' h

/-- **Private witness blocks over the naturals.** If the call blocks of `φ` are pairwise disjoint
and avoid the free polynomials, the natural private-block statement is `φ^♮`. -/
theorem exists_nholds_iff (φ : Formula) (hφ : φ.Scoped) (x : ℕ → ℕ) :
    (∃ y : ℕ → ℕ, (∀ i, ¬ InBlocks φ.blocks i → y i = x i) ∧ NHolds y φ) ↔ NLift x φ := by
  classical
  induction φ using Formula.induct' generalizing x with
  | eq a b =>
    simp only [Formula.blocks, InBlocks, List.not_mem_nil, false_and, exists_false,
      not_false_eq_true, forall_const, nholds_eq, nlift_eq]
    exact ⟨fun ⟨y, hy, h⟩ => (funext hy : y = x) ▸ h, fun h => ⟨x, fun _ => rfl, h⟩⟩
  | atom f =>
    simp only [Formula.blocks, InBlocks, List.not_mem_nil, false_and, exists_false,
      not_false_eq_true, forall_const, nholds_atom, nlift_atom]
    exact ⟨fun ⟨y, hy, h⟩ => (funext hy : y = x) ▸ h, fun h => ⟨x, fun _ => rfl, h⟩⟩
  | call τ g w =>
    have hτ : τ.WF := hφ.wf τ (by simp [Formula.callees])
    have hblock : ∀ i, InBlocks (Formula.call τ g w).blocks i ↔
        w ≤ i ∧ i < w + τ.witnesses := by
      intro i; simp [Formula.blocks, InBlocks, InBlock]
    have hg : ∀ j, ∀ i ∈ (g j).vars, i < w ∨ w + τ.witnesses ≤ i := by
      intro j i hi
      have := hφ.free (g j) (by simp [Formula.freePolys]) i hi
      rw [hblock] at this
      omega
    rw [nlift_call, ← exists_call_iff hτ g w hg x]
    simp only [nholds_call, hblock]
  | and fs ih =>
    have hsub : ∀ φ ∈ fs, φ.Scoped := fun φ hφ' => by
      have := hφ; obtain ⟨h1, h2, h3⟩ := this
      simp only [Formula.callees_and, Formula.blocks_and, Formula.freePolys_and] at h1 h2 h3
      exact Formula.Scoped.of_mem hφ' h1 h2 h3
    have hfree : ∀ φ ∈ fs, ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, ¬ InBlocks (fs.flatMap Formula.blocks) i :=
      fun φ hφ' f hf i hi => by
        have := hφ.free f (by rw [Formula.freePolys_and]; exact List.mem_flatMap.2 ⟨φ, hφ', hf⟩) i hi
        rwa [Formula.blocks_and] at this
    simp only [Formula.blocks_and, nholds_and, nlift_and]
    constructor
    · rintro ⟨y, hy, h⟩ φ hφ'
      refine (ih φ hφ' (hsub φ hφ') x).1
        ⟨fun i => if InBlocks φ.blocks i then y i else x i, fun i hi => ?_, ?_⟩
      · simp only [hi, ite_false]
      · refine (nholds_restrict (hsub φ hφ') fun f hf i hi => ?_).2 (h φ hφ')
        exact hy i (hfree φ hφ' f hf i hi)
    · intro h
      have hY : ∀ φ (hφ' : φ ∈ fs), ∃ y : ℕ → ℕ,
          (∀ i, ¬ InBlocks φ.blocks i → y i = x i) ∧ NHolds y φ :=
        fun φ hφ' => (ih φ hφ' (hsub φ hφ') x).2 (h φ hφ')
      choose Y hYx hYh using hY
      have hdisj := (List.pairwise_flatMap.1 (by simpa using hφ.disjoint)).2
      have : Std.Symm fun a b : Formula =>
          ∀ x ∈ a.blocks, ∀ y ∈ b.blocks, BlockDisjoint x y :=
        ⟨fun _ _ h x hx y hy => Std.Symm.symm _ _ (h y hy x hx)⟩
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
      · refine (nholds_congr fun i hi => ?_).1 (hYh φ hφ')
        rcases Formula.mem_vars_compile (hsub φ hφ').wf hi with ⟨f, hf, hif⟩ | hb
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
      simp only [Formula.callees_or, Formula.blocks_or, Formula.freePolys_or] at h1 h2 h3
      exact Formula.Scoped.of_mem hφ' h1 h2 h3
    have hfree : ∀ φ ∈ fs, ∀ f ∈ φ.freePolys, ∀ i ∈ f.vars, ¬ InBlocks (fs.flatMap Formula.blocks) i :=
      fun φ hφ' f hf i hi => by
        have := hφ.free f (by rw [Formula.freePolys_or]; exact List.mem_flatMap.2 ⟨φ, hφ', hf⟩) i hi
        rwa [Formula.blocks_or] at this
    simp only [Formula.blocks_or, nholds_or, nlift_or]
    constructor
    · rintro ⟨y, hy, φ, hφ', h⟩
      refine ⟨φ, hφ', (ih φ hφ' (hsub φ hφ') x).1
        ⟨fun i => if InBlocks φ.blocks i then y i else x i, fun i hi => ?_, ?_⟩⟩
      · simp only [hi, ite_false]
      · refine (nholds_restrict (hsub φ hφ') fun f hf i hi => ?_).2 h
        exact hy i (hfree φ hφ' f hf i hi)
    · rintro ⟨φ, hφ', h⟩
      obtain ⟨y, hy, hh⟩ := (ih φ hφ' (hsub φ hφ') x).2 h
      exact ⟨y, fun i hi => hy i fun hb => hi (inBlocks_flatMap.2 ⟨φ, hφ', hb⟩), φ, hφ', hh⟩

/-! ### The three items -/

/-- **Item 1.** The natural circuit of a construction that preserves the scope invariant and
whose node encoding is valid is well scoped, its variable count is the final counter, and its
polynomial is `κ(φ)`. -/
theorem toCircuit_item1 {k : ℕ} {m : NM NForm} (T : ExPoly) (hpres : Pres k m)
    {P : State → Prop} (hP : P (State.init k)) (hm : Triple P m fun φ s => φ.Valid T s) :
    (m.toCircuit k).WellScoped ∧ (m.toCircuit k).varCount = (m (State.init k)).2.next ∧
      (m.toCircuit k).poly T = (m.formula T k).compile := by
  refine ⟨toCircuit_wellScoped hpres, ?_, toCircuit_poly hP hm⟩
  rw [NM.toCircuit_varCount, (counts_encode ExPoly.empty _ _).1]
  rfl

/-- **Item 2.** If moreover the call blocks of the final formula are private and lie above the
inputs, and its compilation has its variables below the variable count, then `Z_𝒞(c)` holds iff
some natural values of the variables, equal to `c` on the inputs, satisfy `φ^♮`. -/
theorem toCircuit_natRel_iff {k : ℕ} {m : NM NForm} {T : ExPoly} {P : State → Prop}
    (hP : P (State.init k)) (hm : Triple P m fun φ s => φ.Valid T s)
    (hk : k ≤ (m.toCircuit k).varCount) (hscoped : (m.formula T k).Scoped)
    (hblocks : ∀ b ∈ (m.formula T k).blocks, k ≤ b.1)
    (hvars : VarsLT (m.formula T k).compile (m.toCircuit k).varCount) (c : Fin k → ℕ) :
    (m.toCircuit k).NatRel T c ↔
      ∃ y : ℕ → ℕ, (∀ i : Fin k, y i = c i) ∧ NLift y (m.formula T k) := by
  classical
  refine (Packed.natRel_iff_agree (m.toCircuit k) T hk c).trans ?_
  have hk' : (m.toCircuit k).inputCount = k := rfl
  generalize hx : NatCircuit.natPoint (m.toCircuit k).inputCount
    ((m.toCircuit k).varCount - (m.toCircuit k).inputCount) c (fun _ => 0) = x
  have hxc : ∀ i : Fin k, x i = c i := fun i => by
    rw [← hx]; simp only [NatCircuit.natPoint, hk']; simp [i.isLt]; rfl
  rw [hk', toCircuit_poly hP hm]
  simp only [compile_zv_eq_zero_iff]
  generalize m.formula T k = φ at hscoped hblocks hvars
  generalize (m.toCircuit k).varCount = V at hvars
  constructor
  · rintro ⟨y, hy, hφ⟩
    refine ⟨y, fun i => by rw [hy i (by have := i.isLt; omega), hxc], ?_⟩
    exact (exists_nholds_iff φ hscoped y).1 ⟨y, fun _ _ => rfl, hφ⟩
  · rintro ⟨y, hyc, hφ⟩
    obtain ⟨y', hy', hφ'⟩ := (exists_nholds_iff φ hscoped y).2 hφ
    refine ⟨fun i => if k ≤ i ∧ i < V then y' i else x i, fun i hi => by simp [hi], ?_⟩
    refine (nholds_congr fun i hi => ?_).1 hφ'
    have hiV := hvars i hi
    split_ifs with h
    · rfl
    · have hik : i < k := by omega
      have hnb : ¬ InBlocks φ.blocks i := fun ⟨b, hb, hib⟩ => by
        have := hblocks b hb; simp only [InBlock] at hib; omega
      rw [hy' i hnb, hyc ⟨i, hik⟩, hxc ⟨i, hik⟩]

/-- In `φ^♮`, a call of the power template at natural values means `P = Q^R`. -/
theorem nlift_call_powerTemplate (x : ℕ → ℕ) (g : Fin 3 → Poly) (w : ℕ) (hg : ∀ j, IsNat (g j)) :
    NLift x (.call powerTemplate g w) ↔ nv x (g 0) = nv x (g 1) ^ nv x (g 2) := by
  refine (nlift_call x powerTemplate g w).trans ?_
  rw [← powerTemplateSem]
  have : (fun j : Fin powerTemplate.params => zv x (g j)) =
      natArgs (nv x (g 0)) (nv x (g 1)) (nv x (g 2)) powerTemplate.params := by
    funext j
    fin_cases j <;> simp [natArgs, (hg _).zv_eq]
  rw [this]

end ZInQ.Compiler.Natural
