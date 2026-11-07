import ZInQKernel.Compiler.NodeCheck.Packed
import ZInQKernel.Compiler.Universal.NodeCheck

/-!
# The Boolean node check of the halting circuit

`haltingNodeCheckB` runs the fast builder on the universal interpreter and counts, in one pass
over the reversed node list, the variable, constant, addition and multiplication nodes and
collects the constants. `haltingNodeCheck_of_checkB` derives `HaltingNodeCheck` from
`haltingNodeCheckB = true`. Each step of the counting pass tests the counter it increments
(`bif v.beq 0 then … else …`, both branches equal), so that an evaluator that reduces lazily
never accumulates long chains of additions.
-/

namespace ZInQ.Compiler.NodeCheck

open Natural Universal

/-- One pass over a node list: the counts of variable, constant, addition and multiplication
nodes added to `v, c, a, m`, and the constants pushed onto `cs`. -/
def countGo : List NatNode → ℕ → ℕ → ℕ → ℕ → List ℤ → ℕ × ℕ × ℕ × ℕ × List ℤ
  | [], v, c, a, m, cs => (v, c, a, m, cs)
  | .var _ :: l, v, c, a, m, cs =>
    bif v.beq 0 then countGo l (v + 1) c a m cs else countGo l (v + 1) c a m cs
  | .const z :: l, v, c, a, m, cs =>
    bif c.beq 0 then countGo l v (c + 1) a m (z :: cs) else countGo l v (c + 1) a m (z :: cs)
  | .add _ _ :: l, v, c, a, m, cs =>
    bif a.beq 0 then countGo l v c (a + 1) m cs else countGo l v c (a + 1) m cs
  | .mul _ _ :: l, v, c, a, m, cs =>
    bif m.beq 0 then countGo l v c a (m + 1) cs else countGo l v c a (m + 1) cs
  | .call _ _ _ _ :: l, v, c, a, m, cs => countGo l v c a m cs

theorem countGo_eq (l : List NatNode) (v c a m : ℕ) (cs : List ℤ) :
    countGo l v c a m cs = (v + countKind .var l, c + countKind .const l,
      a + countKind .add l, m + countKind .mul l, (constList l).reverse ++ cs) := by
  induction l generalizing v c a m cs with
  | nil => rfl
  | cons n l ih =>
    cases n <;>
      simp only [countGo, Bool.cond_self, ih, countKind, List.countP_cons, nodeKind,
        constList, List.filterMap_cons, constOf, Prod.mk.injEq] <;>
      simp <;> omega

/-- The counts of `HaltingNodeCheck`, on the reversed node list `l`. -/
def statsCheck (l : List NatNode) : Bool :=
  match countGo l 0 0 0 0 [] with
  | (v, c, a, m, cs) =>
    v.beq 54049 && c.beq 6 && a.beq 125307 && m.beq 98361 && cs == [0, 1, 2, 4, 1399, -1]

/-- **The Boolean node check**: the fast builder run on `𝒰` with `204` registers and `2`
inputs, and the counts of its node list. -/
def haltingNodeCheckB : Bool := statsCheck (fastNodesRev interpreter 204 2)

theorem countKind_reverse (κ : NodeKind) (l : List NatNode) :
    countKind κ l.reverse = countKind κ l := List.countP_reverse ..

theorem constList_reverse (l : List NatNode) : constList l.reverse = (constList l).reverse :=
  List.filterMap_reverse ..

theorem statsCheck_sound {l L : List NatNode} (hL : L = l.reverse) (h : statsCheck l = true) :
    countKind .var L = 54049 ∧ countKind .const L = 6 ∧ countKind .add L = 125307 ∧
      countKind .mul L = 98361 ∧ constList L = [0, 1, 2, 4, 1399, -1] := by
  unfold statsCheck at h
  rw [countGo_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, Nat.zero_add, List.append_nil] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  subst hL
  rw [countKind_reverse, countKind_reverse, countKind_reverse, countKind_reverse,
    constList_reverse]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Soundness of the Boolean node check.** -/
theorem haltingNodeCheck_of_checkB (h : haltingNodeCheckB = true) : HaltingNodeCheck :=
  statsCheck_sound (L := haltingCircuit.nodes) (compiled_nodes interpreter 204 2) h

theorem countKind_var_eq (l : List NatNode) : countKind .var l = l.countP isVarNode := by
  unfold countKind
  congr 1
  funext n
  cases n <;> rfl

/-- **The variable-node count of the halting circuit**, `54,049` (the first item of
`HaltingNodeCheck`), proved without evaluating the construction: the variable nodes are as
many as the explicit variables. -/
theorem haltingCircuit_varNodes : countKind .var haltingCircuit.nodes = 54049 := by
  rw [countKind_var_eq]
  exact (compiled_varNodes interpreter 204 2).trans haltingCircuit_counts.2.1

end ZInQ.Compiler.NodeCheck
