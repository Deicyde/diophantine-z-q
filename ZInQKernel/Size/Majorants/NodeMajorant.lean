import ZInQKernel.Size.Majorants.Rules
import ZInQKernel.Size.Majorants.Height

/-!
# Templates satisfy the height majorant

Blueprint: `size/majorants/node-majorant.md`.

For a node-list library (`ZInQKernel.Syntax.Language.Nodes`) and `B ≥ 2^20`, if every
constant, fixed, psi and guard node satisfies the four admissibility conditions of the
blueprint (`NodeAdmissible`) and the constructors satisfy the uniform bounds `deg ≤ B^4`,
`‖·‖₁ ≤ 2^(B^8)` at the admissible indices (`ConstructorBounds`, supplied for the concrete
constructors by the norms chapter), then every node satisfies the majorant at its height and
every template at its intrinsic height (`nodes_majorant`, `library_majorant`).

The values `val(e)` enter only through the hypotheses and are never computed.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {E : Type}

/-- The uniform bounds for the finite constructors at the cutoff `B`: `Ψ_{n,c}` for
`|n| + 1 ≤ B` and `G_T` for `0 ≤ T ≤ B - 1` have degree at most `B^4` and norm at most
`2^(B^8)`. -/
structure ConstructorBounds (I : Constructors E) (B : ℕ) : Prop where
  psi : ∀ n : ℤ, n.natAbs + 1 ≤ B → ∀ c,
    (I.psi n c).totalDegree ≤ B ^ 4 ∧ l1 (I.psi n c) ≤ 2 ^ B ^ 8
  guard : ∀ T : ℤ, 0 ≤ T → T.natAbs + 1 ≤ B →
    (I.guard T).totalDegree ≤ B ^ 4 ∧ l1 (I.guard T) ≤ 2 ^ B ^ 8

/-- The four hypotheses of the template majorant on one node: `|c| ≤ B - 1` for a constant,
`|val(e)| ≤ B - 1` for a fixed node, `|val(e)| + 1 ≤ B` for a psi node and
`0 ≤ val(e) ≤ B - 1` for a guard node. -/
def NodeAdmissible (I : Constructors E) (B : ℕ) : Node E → Prop
  | .const c => c.natAbs + 1 ≤ B
  | .fixed e => (I.val e).natAbs + 1 ≤ B
  | .psi e _ _ => (I.val e).natAbs + 1 ≤ B
  | .guard e _ => 0 ≤ I.val e ∧ (I.val e).natAbs + 1 ≤ B
  | _ => True

theorem natAbs_le_two_pow_pow_eight {B : ℕ} {c : ℤ} (hc : c.natAbs + 1 ≤ B) :
    c.natAbs ≤ 2 ^ B ^ 8 :=
  (Nat.le_of_succ_le hc).trans ((Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by norm_num) B)))

theorem getD_append_singleton {α : Type*} (l : List α) (a d : α) (j : ℕ) :
    (l ++ [a]).getD j d = if j < l.length then l.getD j d else if j = l.length then a else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

variable {B : ℕ} {I : Constructors E}

/-- **Nodes satisfy the majorant.** If every template of the library `lib` satisfies the
majorant at its height in `lH`, then every node of an admissible node list satisfies the
majorant at its height. -/
theorem nodes_majorant (hB : 2 ^ 20 ≤ B) (hI : ConstructorBounds I B) {lib : List ExPoly}
    {lH : List ℕ} (hlib : ∀ t, Maj B (lH.getD t 0) (getEx lib t).poly) (nodes : List (Node E))
    (hadm : ∀ n ∈ nodes, NodeAdmissible I B n) :
    ∀ j, Maj B ((nodeHeights lH nodes).getD j 0) (getPoly (denoteNodes I lib nodes) j) := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  induction nodes using List.reverseRecOn with
  | nil => intro j; simpa [nodeHeights, denoteNodes, getPoly] using Maj.zero (σ := ℕ) 0 hB1
  | append_singleton nodes n ih =>
    have ih' := ih fun m hm => hadm m (List.mem_append_left _ hm)
    have hn : NodeAdmissible I B n := hadm n (List.mem_append_right _ List.mem_cons_self)
    set hs := nodeHeights lH nodes
    set vals := denoteNodes I lib nodes
    have hlen : hs.length = vals.length := by
      simp only [hs, vals, length_nodeHeights, length_denoteNodes]
    intro j
    rw [nodeHeights_append, denoteNodes_append, getPoly, getD_append_singleton,
      getD_append_singleton, ← hlen]
    split_ifs with h1 h2
    · exact ih' j
    · -- the new node
      have hval : ∀ j, Maj B (hs.getD j 0) (vals.getD j 0) := ih'
      cases n with
      | const c => exact Maj.C (natAbs_le_two_pow_pow_eight hn)
      | var i => exact Maj.X i
      | add j k =>
        exact Maj.add hB (hval j) (hval k)
      | mul j k =>
        exact Maj.mul hB (hval j) (hval k)
      | call t args w =>
        show Maj B (1 + lH.getD t 0 + listMax (args.map fun j => hs.getD j 0))
          (callPoly (getEx lib t).poly (getEx lib t).params w
            (fun i => getPoly (args.map (getPoly vals)) i))
        rw [show 1 + lH.getD t 0 + listMax (args.map fun j => hs.getD j 0) =
          lH.getD t 0 + listMax (args.map fun j => hs.getD j 0) + 1 by ring]
        refine Maj.bind₁ hB (hlib t) fun i _ => ?_
        unfold callSubst
        split_ifs with hi
        · show Maj B _ ((args.map (getPoly vals)).getD i 0)
          by_cases hia : i < args.length
          · rw [List.getD_eq_getElem _ _ (by simpa using hia), List.getElem_map]
            exact (hval _).mono (le_listMax (List.mem_map.2 ⟨_, List.getElem_mem hia, rfl⟩)) hB1
          · rw [List.getD_eq_default _ _ (by simpa using hia)]
            exact Maj.zero _ hB1
        · exact (Maj.X _).mono (Nat.zero_le _) hB1
      | fixed e => exact Maj.C (natAbs_le_two_pow_pow_eight hn)
      | psi e a c =>
        show Maj B (1 + listMax (List.ofFn fun i => hs.getD (a i) 0))
          (bind₁ (fun i => getPoly vals (a i)) (I.psi (I.val e) c))
        rw [add_comm]
        exact Maj.constructor hB (hI.psi _ hn c).1 (hI.psi _ hn c).2 fun i _ =>
          (hval (a i)).mono (le_listMax (List.mem_ofFn.2 ⟨i, rfl⟩)) hB1
      | guard e a =>
        show Maj B (1 + listMax (List.ofFn fun i => hs.getD (a i) 0))
          (bind₁ (fun i => getPoly vals (a i)) (I.guard (I.val e)))
        rw [add_comm]
        exact Maj.constructor hB (hI.guard _ hn.1 hn.2).1 (hI.guard _ hn.1 hn.2).2 fun i _ =>
          (hval (a i)).mono (le_listMax (List.mem_ofFn.2 ⟨i, rfl⟩)) hB1
    · exact Maj.zero 0 hB1

theorem denoteLibrary_append (I : Constructors E) (ts : List (Template E)) (t : Template E) :
    denoteLibrary I (ts ++ [t]) = denoteLibrary I ts ++ [t.denote I (denoteLibrary I ts)] := by
  simp [denoteLibrary, List.foldl_append]

theorem length_denoteLibrary (I : Constructors E) (ts : List (Template E)) :
    (denoteLibrary I ts).length = ts.length := by
  induction ts using List.reverseRecOn with
  | nil => rfl
  | append_singleton ts t ih => simp [denoteLibrary_append, ih]

/-- **Templates satisfy the height majorant.** For an admissible library, every template
satisfies the majorant at its intrinsic height. -/
theorem library_majorant (hB : 2 ^ 20 ≤ B) (hI : ConstructorBounds I B) (ts : List (Template E))
    (hadm : ∀ t ∈ ts, ∀ n ∈ t.nodes, NodeAdmissible I B n) :
    ∀ i, Maj B ((libraryHeights ts).getD i 0) (getEx (denoteLibrary I ts) i).poly := by
  have hB1 := one_le_of_two_pow_twenty_le hB
  induction ts using List.reverseRecOn with
  | nil => intro i; simpa [libraryHeights, denoteLibrary, getEx, ExPoly.empty] using
      Maj.zero (σ := ℕ) 0 hB1
  | append_singleton ts t ih =>
    have ih' := ih fun u hu => hadm u (List.mem_append_left _ hu)
    have ht : ∀ n ∈ t.nodes, NodeAdmissible I B n :=
      hadm t (List.mem_append_right _ List.mem_cons_self)
    have hlen : (libraryHeights ts).length = (denoteLibrary I ts).length := by
      rw [length_libraryHeights, length_denoteLibrary]
    intro i
    rw [libraryHeights_append, denoteLibrary_append, getEx, getD_append_singleton,
      getD_append_singleton, ← hlen]
    split_ifs with h1 h2
    · exact ih' i
    · exact nodes_majorant hB hI ih' t.nodes ht t.root
    · exact Maj.zero 0 hB1

/-- The majorant for every node of every template of an admissible library: node `j` of
template `i` satisfies the majorant at its height. -/
theorem library_nodes_majorant (hB : 2 ^ 20 ≤ B) (hI : ConstructorBounds I B)
    (ts : List (Template E)) (hadm : ∀ t ∈ ts, ∀ n ∈ t.nodes, NodeAdmissible I B n) {i : ℕ}
    (hi : i < ts.length) (j : ℕ) :
    Maj B ((nodeHeights (libraryHeights (ts.take i)) ts[i].nodes).getD j 0)
      (getPoly (denoteNodes I (denoteLibrary I (ts.take i)) ts[i].nodes) j) :=
  nodes_majorant hB hI
    (library_majorant hB hI (ts.take i) fun t ht => hadm t (List.mem_of_mem_take ht))
    ts[i].nodes (hadm _ (List.getElem_mem hi)) j

end ZInQ.Size
