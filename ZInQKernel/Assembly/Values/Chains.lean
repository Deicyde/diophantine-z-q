import ZInQKernel.Assembly.Values.Lift
import ZInQKernel.Compiler.Translation.Points

/-!
# Double-and-add chains

Blueprint: `assembly/value-templates/double-and-add-chains.md`.

The chain `chainBuild out base ds` of the exceptional-values template runs over the binary
digits `ds` (least significant first): for a digit `1` it takes a fresh point `σ` with the call
`raw_add[out, base, σ]`, and while digits remain it takes a fresh point `δ` with
`raw_add[base, base, δ]`. Started at `out = ι(a)`, `base = ι(m)`, every assignment satisfying
the raw additions of the chain gives the value `ι(a + k m)`, `k = Σ dᵢ 2ⁱ` (`chain_value`), and
such an assignment exists (`chain_satisfiable`). For `out = O` and the digits of `k`
(`binDigits k`) the value is `ι(k m)` (`chainBuild_binDigits_value`).
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial Translation

/-- The value `Σ dᵢ 2ⁱ` of binary digits, least significant first. -/
def binVal : List Bool → ℕ
  | [] => 0
  | d :: ds => (if d then 1 else 0) + 2 * binVal ds

theorem binVal_binDigitsAux (fuel k : ℕ) (h : k ≤ fuel) : binVal (binDigitsAux fuel k) = k := by
  induction fuel generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ f ih =>
    by_cases hk : k = 0
    · subst hk; rfl
    · simp only [binDigitsAux, hk, ite_false, binVal]
      rw [ih (k / 2) (by omega)]
      by_cases h2 : k % 2 = 1 <;> simp [h2] <;> omega

/-- The digits of `k` have value `k`. -/
theorem binVal_binDigits (k : ℕ) : binVal (binDigits k) = k :=
  binVal_binDigitsAux k k le_rfl

/-- The number of raw additions of the chain: one per digit `1`, and one doubling per digit
except the last. -/
def chainCount : List Bool → ℕ
  | [] => 0
  | [d] => if d then 1 else 0
  | d :: d' :: ds => (if d then 1 else 0) + 1 + chainCount (d' :: ds)

/-! ### One step of the chain -/

@[simp] theorem _root_.ZInQ.Syntax.BuildState.next_mk (n : ℕ) (g : List (ℕ × ℤ × ℤ)) :
    ({ next := n, globals := g } : BuildState).next = n := rfl

theorem chainBuild_nil (out base : Code) (s : BuildState) :
    chainBuild out base [] s = ((out, []), s) := rfl

theorem chainBuild_true_nil (out base : Code) (s : BuildState) :
    chainBuild out base [true] s =
      ((varPoint s.next,
        [Formula.call rawAddTemplate (Fin.append (Fin.append out base) (varPoint s.next))
          (s.next + 5)]), ⟨s.next + 5 + 6, s.globals⟩) := rfl

theorem chainBuild_false_nil (out base : Code) (s : BuildState) :
    chainBuild out base [false] s = ((out, []), s) := rfl

theorem chainBuild_true_cons (out base : Code) (d : Bool) (ds : List Bool) (s : BuildState) :
    chainBuild out base (true :: d :: ds) s =
      let r := chainBuild (varPoint s.next) (varPoint (s.next + 5 + 6)) (d :: ds)
        ⟨s.next + 5 + 6 + 5 + 6, s.globals⟩
      ((r.1.1, [Formula.call rawAddTemplate (Fin.append (Fin.append out base) (varPoint s.next))
          (s.next + 5)] ++
        [Formula.call rawAddTemplate (Fin.append (Fin.append base base)
          (varPoint (s.next + 5 + 6))) (s.next + 5 + 6 + 5)] ++ r.1.2), r.2) := rfl

theorem chainBuild_false_cons (out base : Code) (d : Bool) (ds : List Bool) (s : BuildState) :
    chainBuild out base (false :: d :: ds) s =
      let r := chainBuild out (varPoint s.next) (d :: ds) ⟨s.next + 5 + 6, s.globals⟩
      ((r.1.1, [] ++ [Formula.call rawAddTemplate (Fin.append (Fin.append base base)
          (varPoint s.next)) (s.next + 5)] ++ r.1.2), r.2) := rfl

/-- The chain keeps the rational constants and only advances the counter. -/
theorem chainBuild_state (ds : List Bool) :
    ∀ (out base : Code) (s : BuildState),
      (chainBuild out base ds s).2.globals = s.globals ∧ s.next ≤ (chainBuild out base ds s).2.next := by
  induction ds with
  | nil => intro out base s; exact ⟨rfl, le_rfl⟩
  | cons d ds ih =>
    intro out base s
    cases ds with
    | nil => cases d <;> simp [chainBuild_true_nil, chainBuild_false_nil] <;> omega
    | cons d' ds' =>
      cases d
      · rw [chainBuild_false_cons]
        obtain ⟨h1, h2⟩ := ih out (varPoint s.next) ⟨s.next + 5 + 6, s.globals⟩
        exact ⟨h1, by simp only at h2 ⊢; omega⟩
      · rw [chainBuild_true_cons]
        obtain ⟨h1, h2⟩ := ih (varPoint s.next) (varPoint (s.next + 5 + 6))
          ⟨s.next + 5 + 6 + 5 + 6, s.globals⟩
        exact ⟨h1, by simp only at h2 ⊢; omega⟩

/-- The number of raw additions of the chain. -/
theorem chainBuild_length (ds : List Bool) :
    ∀ (out base : Code) (s : BuildState), (chainBuild out base ds s).1.2.length = chainCount ds := by
  induction ds with
  | nil => intro out base s; rfl
  | cons d ds ih =>
    intro out base s
    cases ds with
    | nil => cases d <;> rfl
    | cons d' ds' =>
      cases d
      · rw [chainBuild_false_cons]
        simp only [List.length_append, List.length_nil, List.length_singleton, ih, chainCount]
        simp
      · rw [chainBuild_true_cons]
        simp only [List.length_append, List.length_singleton, ih, chainCount]
        simp

/-- The chains of the six contact values have `0, 7, 6, 6, 8, 9` raw additions. -/
theorem chainCount_contacts :
    (chainCount (binDigits 0), chainCount (binDigits 15), chainCount (binDigits 20),
      chainCount (binDigits 24), chainCount (binDigits 30), chainCount (binDigits 60)) =
      (0, 7, 6, 6, 8, 9) := by
  obtain ⟨h0, h15, h20, h24, h30, h60⟩ := binDigits_contacts
  rw [h0, h15, h20, h24, h30, h60]
  rfl

/-! ### Soundness -/

/-- **Double-and-add chains, soundness.** If `out = ι(a)` and `base = ι(m)` and all raw
additions of the chain hold, its value is `ι(a + k m)` with `k = Σ dᵢ 2ⁱ`. -/
theorem chain_value (ds : List Bool) :
    ∀ (out base : Code) (s : BuildState) (y : ℕ → ℚ) (a m : ℤ),
      evCode y out = iota a → evCode y base = iota m →
      (∀ φ ∈ (chainBuild out base ds s).1.2, φ.Lift y) →
      evCode y (chainBuild out base ds s).1.1 = iota (a + binVal ds * m) := by
  induction ds with
  | nil =>
    intro out base s y a m ho _ _
    simpa [chainBuild_nil, binVal] using ho
  | cons d ds ih =>
    intro out base s y a m ho hb h
    cases ds with
    | nil =>
      cases d
      · simpa [chainBuild_false_nil, binVal] using ho
      · rw [chainBuild_true_nil] at h ⊢
        have := (lift_rawAdd_code _ _ _ _ _).1 (h _ List.mem_cons_self)
        rw [ho, hb, rel_rawAdd_iota] at this
        simpa [binVal] using this
    | cons d' ds' =>
      cases d
      · rw [chainBuild_false_cons] at h ⊢
        simp only [List.nil_append, List.mem_append, List.mem_singleton] at h
        have hδ := (lift_rawAdd_code _ _ _ _ _).1 (h _ (Or.inl rfl))
        rw [hb, rel_rawAdd_iota] at hδ
        rw [ih out _ _ y a (m + m) ho hδ fun φ hφ => h φ (Or.inr hφ)]
        congr 1
        simp only [binVal]
        push_cast
        ring
      · rw [chainBuild_true_cons] at h ⊢
        simp only [List.mem_append, List.mem_singleton] at h
        have hσ := (lift_rawAdd_code _ _ _ _ _).1 (h _ (Or.inl (Or.inl rfl)))
        have hδ := (lift_rawAdd_code _ _ _ _ _).1 (h _ (Or.inl (Or.inr rfl)))
        rw [ho, hb, rel_rawAdd_iota] at hσ
        rw [hb, rel_rawAdd_iota] at hδ
        rw [ih _ _ _ y (a + m) (m + m) hσ hδ fun φ hφ => h φ (Or.inr hφ)]
        congr 1
        simp only [binVal]
        push_cast
        ring

/-! ### Completeness -/

theorem evCode_writePoints_of_lt {y : ℕ → ℚ} {l : List (ℕ × (Fin 5 → ℚ))} {p : Code} {n : ℕ}
    (hp : ∀ i, VarsIn (p i) (· < n)) (hl : ∀ e ∈ l, n ≤ e.1) :
    evCode (writePoints y l) p = evCode y p :=
  evCode_congr fun i j hj =>
    writePoints_of_not_mem y l fun e he h => by have := hp i j hj; have := hl e he; omega

theorem varsIn_varPoint {k n : ℕ} (h : k + 5 ≤ n) (i : Fin 5) : VarsIn (varPoint k i) (· < n) :=
  VarsIn.X (show k + (i : ℕ) < n by have := i.isLt; omega)

theorem VarsIn.code_mono {p : Code} {n n' : ℕ} (h : ∀ i, VarsIn (p i) (· < n)) (hn : n ≤ n') :
    ∀ i, VarsIn (p i) (· < n') :=
  fun i => (h i).mono fun _ hj => lt_of_lt_of_le hj hn

/-- **Double-and-add chains, completeness.** If `out = ι(a)` and `base = ι(m)` have their
variables below the counter, the fresh points of the chain can be chosen, without changing
the variables below the counter, so that all raw additions of the chain hold. -/
theorem chain_satisfiable (ds : List Bool) :
    ∀ (out base : Code) (s : BuildState) (y : ℕ → ℚ) (a m : ℤ),
      (∀ i, VarsIn (out i) (· < s.next)) → (∀ i, VarsIn (base i) (· < s.next)) →
      evCode y out = iota a → evCode y base = iota m →
      ∃ y' : ℕ → ℚ, (∀ i < s.next, y' i = y i) ∧
        ∀ φ ∈ (chainBuild out base ds s).1.2, φ.Lift y' := by
  induction ds with
  | nil => intro out base s y a m _ _ _ _; exact ⟨y, fun _ _ => rfl, by simp [chainBuild_nil]⟩
  | cons d ds ih =>
    intro out base s y a m hvo hvb ho hb
    cases ds with
    | nil =>
      cases d
      · exact ⟨y, fun _ _ => rfl, by simp [chainBuild_false_nil]⟩
      · rw [chainBuild_true_nil]
        let l : List (ℕ × (Fin 5 → ℚ)) := [(s.next, iota (a + m))]
        refine ⟨writePoints y l, fun i hi => writePoints_of_not_mem y l (fun e he => by
          simp only [l, List.mem_singleton] at he; subst he; simp only; omega), ?_⟩
        simp only [List.mem_singleton, forall_eq]
        have hσ : evCode (writePoints y l) (varPoint s.next) = iota (a + m) := by
          rw [evCode_varPoint]
          exact writePoints_point y (by simp [l]) (by simp [l])
        rw [lift_rawAdd_code, evCode_writePoints_of_lt hvo (by simp [l]),
          evCode_writePoints_of_lt hvb (by simp [l]), hσ, ho, hb, rel_rawAdd_iota]
    | cons d' ds' =>
      cases d
      · rw [chainBuild_false_cons]
        let l : List (ℕ × (Fin 5 → ℚ)) := [(s.next, iota (m + m))]
        have hl1 : ∀ i < s.next, writePoints y l i = y i :=
          fun i hi => writePoints_of_not_mem y l (by simp [l]; omega)
        have hδ : evCode (writePoints y l) (varPoint s.next) = iota (m + m) := by
          rw [evCode_varPoint]
          exact writePoints_point y (by simp [l]) (by simp [l])
        obtain ⟨y', hy', h⟩ := ih out (varPoint s.next) ⟨s.next + 5 + 6, s.globals⟩
          (writePoints y l) a (m + m)
          (VarsIn.code_mono hvo (show s.next ≤ s.next + 5 + 6 by omega))
          (varsIn_varPoint (show s.next + 5 ≤ s.next + 5 + 6 by omega))
          (by rw [evCode_writePoints_of_lt hvo (by simp [l]), ho]) hδ
        refine ⟨y', fun i hi => (hy' i (by simp only ; omega)).trans (hl1 i hi), ?_⟩
        simp only [List.nil_append, List.mem_append, List.mem_singleton]
        rintro φ (rfl | hφ)
        · have e1 : evCode y' base = evCode y base :=
            evCode_congr fun i j hj => by
              have := hvb i j hj; simp only at this
              exact (hy' j (by simp only ; omega)).trans (hl1 j this)
          have e2 : evCode y' (varPoint s.next) = evCode (writePoints y l) (varPoint s.next) :=
            evCode_congr fun i j hj => hy' j (by
              have := varsIn_varPoint (k := s.next) (n := s.next + 5) le_rfl i j hj
              simp only at this ⊢; omega)
          rw [lift_rawAdd_code, e1, e2, hδ, hb, rel_rawAdd_iota]
        · exact h φ hφ
      · rw [chainBuild_true_cons]
        let l : List (ℕ × (Fin 5 → ℚ)) := [(s.next, iota (a + m)), (s.next + 5 + 6, iota (m + m))]
        have hsep : (l.map Prod.fst).Pairwise Separated := by
          simp [l, Separated]
        have hl1 : ∀ i < s.next, writePoints y l i = y i :=
          fun i hi => writePoints_of_not_mem y l (by simp [l]; omega)
        have hσ : evCode (writePoints y l) (varPoint s.next) = iota (a + m) := by
          rw [evCode_varPoint]
          exact writePoints_point y hsep (by simp [l])
        have hδ : evCode (writePoints y l) (varPoint (s.next + 5 + 6)) = iota (m + m) := by
          rw [evCode_varPoint]
          exact writePoints_point y hsep (by simp [l])
        obtain ⟨y', hy', h⟩ := ih (varPoint s.next) (varPoint (s.next + 5 + 6))
          ⟨s.next + 5 + 6 + 5 + 6, s.globals⟩ (writePoints y l) (a + m) (m + m)
          (varsIn_varPoint (by simp only ; omega)) (varsIn_varPoint (by simp only ; omega)) hσ hδ
        refine ⟨y', fun i hi => (hy' i (by simp only ; omega)).trans (hl1 i hi), ?_⟩
        have eo : ∀ p : Code, (∀ i, VarsIn (p i) (· < s.next)) → evCode y' p = evCode y p :=
          fun p hp => evCode_congr fun i j hj => by
            have := hp i j hj; simp only at this
            exact (hy' j (by simp only ; omega)).trans (hl1 j this)
        have ep : ∀ k, k + 5 ≤ s.next + 5 + 6 + 5 + 6 →
            evCode y' (varPoint k) = evCode (writePoints y l) (varPoint k) :=
          fun k hk => evCode_congr fun i j hj => hy' j (by
            have := varsIn_varPoint (k := k) (n := k + 5) le_rfl i j hj
            simp only at this ⊢; omega)
        simp only [List.mem_append, List.mem_singleton]
        rintro φ ((rfl | rfl) | hφ)
        · rw [lift_rawAdd_code, eo out hvo, eo base hvb, ep _ (by omega), hσ, ho, hb,
            rel_rawAdd_iota]
        · rw [lift_rawAdd_code, eo base hvb, ep _ (by omega), hδ, hb, rel_rawAdd_iota]
        · exact h φ hφ

/-! ### Chains on the digits of `k` -/

/-- The chain for `k` started at `O` on `ι(m)` has value `ι(k m)`. -/
theorem chainBuild_binDigits_value (k : ℕ) (base : Code) (s : BuildState) (y : ℕ → ℚ) (m : ℤ)
    (hb : evCode y base = iota m)
    (h : ∀ φ ∈ (chainBuild Code.O base (binDigits k) s).1.2, φ.Lift y) :
    evCode y (chainBuild Code.O base (binDigits k) s).1.1 = iota (k * m) := by
  rw [chain_value _ _ _ _ y 0 m (evCode_O' y) hb h, binVal_binDigits, zero_add]

end ZInQ.Assembly
