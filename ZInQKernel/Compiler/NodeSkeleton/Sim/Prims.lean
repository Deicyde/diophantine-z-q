import ZInQKernel.Compiler.NodeSkeleton.Sim.Basic

/-!
# The simulation judgment and the primitives

`Sim2 Hall er m m'`: from related states, the fast construction `m` and the checking
construction `m'` end in related states with results related by `er`, whenever the checking
run ends with `ok = true`; and a checking run that ends with `ok = true` started with
`ok = true` (`mono`). Primitives: `fresh`, `constant`, `callPower` and the addition and
multiplication nodes (`nodeOp`).
-/

namespace ZInQ.Compiler.NodeSkeleton

open Natural NodeCheck Universal

/-! ### Appending a node -/

theorem force_eq {α : Type} (n : ℕ) (k : ℕ → α) : force n k = k n := by
  simp [force]

theorem create_eq {k : ℕ} {c : Bool} {nx a m : ℕ} {cs hot : List (ℕ × ℕ)} {codes : List ℕ}
    {lanes : List (List ℕ)} {h : HState} (hok : (create k c nx a m cs hot codes lanes h).ok = true) :
    c = true ∧ h.ok = true ∧ h.len < h.lim ∧
      create k c nx a m cs hot codes lanes h =
        ⟨h.len + 1, nx, a, m, cs, (2 * k + cond (hubStep h.len h.hubs).1 1 0) :: h.win, hot, codes,
          (hubStep h.len h.hubs).2, lanes, h.lim, true⟩ := by
  unfold create at hok ⊢
  rw [force_eq] at hok ⊢
  obtain ⟨f, hubs'⟩ := hubStep h.len h.hubs
  simp only at hok ⊢
  cases h1 : h.ok <;> cases h2 : c <;> cases h3 : h.len.blt h.lim <;> simp_all

theorem nodes_cons (t : FState) (n : NatNode) : (n :: t.rev).reverse = nodesOf t ++ [n] := by
  simp [nodesOf]

theorem getElem?_snoc {l : List NatNode} {n : NatNode} {j : ℕ} {m : NatNode}
    (h : (l ++ [n])[j]? = some m) : (j < l.length ∧ l[j]? = some m) ∨ (j = l.length ∧ m = n) := by
  by_cases hj : j < l.length
  · left; rw [List.getElem?_append_left hj] at h; exact ⟨hj, h⟩
  · right
    rw [List.getElem?_append_right (by omega)] at h
    have : j - l.length = 0 := by
      by_contra hne
      rw [List.getElem?_singleton] at h
      simp [hne] at h
    have hj' : j = l.length := by omega
    subst hj'
    simp at h
    exact ⟨rfl, h.symm⟩

theorem getElem?_lt {l : List NatNode} {j : ℕ} {m : NatNode} (h : l[j]? = some m) : j < l.length := by
  by_contra hj
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

/-- Appending a node `n`: the relation is preserved. -/
theorem Rel.append {Hall Hf : List ℕ} {Ff : ℕ → List ℕ} {t : FState} {h : HState}
    (hr : Rel Hall Hf Ff t h) (n : NatNode) (next' : ℕ) (table' : Table) (adds' muls' : ℕ)
    (consts' hot' : List (ℕ × ℕ)) (codes' : List ℕ) (lanes' : List (List ℕ))
    (hlim : h.len < h.lim)
    (htable : ∀ m, tabled m = true → table'.find m = (nodesOf t ++ [n]).idxOf? m)
    (hnew : tabled n = true → n ∉ nodesOf t)
    (hchild : isOp n = true → youngest n < t.len)
    (hadds : adds' = countKind .add (n :: t.rev)) (hmuls : muls' = countKind .mul (n :: t.rev))
    (hconsts : ∀ c, constFind (lintKey c) consts' = (nodesOf t ++ [n]).idxOf? (.const c))
    (hhot : ∀ e ∈ hot', ∃ m, (nodesOf t ++ [n])[e.2]? = some m ∧ isOp m = true ∧ nodeKey m = e.1)
    (hlanes : ∀ ℓ, ∃ pre, remL Ff h ℓ = pre ++ (lanes'.getD ℓ [] ++ Ff ℓ))
    (hhist : isOp n = true → flagOf Hall (youngest n) = true →
      ∀ ℓ, youngest n * laneBase + nodeKey n ∉ lanes'.getD ℓ [] ++ Ff ℓ)
    (hsorted : HubSorted Hall) :
    Rel Hall Hf Ff ⟨next', table', t.len + 1, n :: t.rev⟩
      ⟨h.len + 1, next', adds', muls', consts',
        (2 * nodeKey n + cond (hubStep h.len h.hubs).1 1 0) :: h.win, hot', codes',
        (hubStep h.len h.hubs).2, lanes', h.lim, true⟩ := by
  obtain ⟨hf1, hf2⟩ := hubStep_spec hsorted hr.hubs hr.hubsLim hlim
  have hlen : h.len = (nodesOf t).length := by simp [nodesOf, hr.len, hr.lenRev]
  refine ⟨by simp [hr.len], rfl, by simp [hr.lenRev], ?_, ?_, ?_, hadds, hmuls, ?_, ?_, ?_, ?_, ?_,
    hr.hubsLim, ?_, ?_, ?_, hsorted⟩
  · intro m hm; rw [nodesOf, nodes_cons]; exact htable m hm
  · intro i j m hi hj hm
    simp only [nodesOf, nodes_cons] at hi hj
    rcases getElem?_snoc hi with ⟨hi1, hi2⟩ | ⟨hi1, rfl⟩ <;>
      rcases getElem?_snoc hj with ⟨hj1, hj2⟩ | ⟨hj1, hj3⟩
    · exact hr.nodup i j m hi2 hj2 hm
    · subst hj3; exact absurd (List.mem_of_getElem? hi2) (hnew hm)
    · exact absurd (List.mem_of_getElem? hj2) (hnew hm)
    · omega
  · intro j m hj hm
    simp only [nodesOf, nodes_cons] at hj
    rcases getElem?_snoc hj with ⟨hj1, hj2⟩ | ⟨hj1, rfl⟩
    · exact hr.child j m hj2 hm
    · have := hchild hm
      rw [hj1]; simp [hr.lenRev] at this ⊢; omega
  · intro c; rw [nodesOf, nodes_cons]; exact hconsts c
  · intro e he; rw [nodesOf, nodes_cons]; exact hhot e he
  · show _ :: h.win <+: (2 * nodeKey n + cond (flagOf Hall t.rev.length) 1 0) :: recsOf Hall t.rev
    rw [hf1, ← hr.lenRev, ← hr.len]
    exact List.cons_prefix_cons.mpr ⟨rfl, hr.win⟩
  · show h.len + 1 ≤ h.lim; omega
  · exact hf2
  · intro ℓ
    obtain ⟨pre, hpre⟩ := hlanes ℓ
    have := hr.laneNodup ℓ
    rw [hpre] at this
    exact (List.nodup_append.mp this).2.1
  · intro ℓ e he
    obtain ⟨pre, hpre⟩ := hlanes ℓ
    apply hr.laneLabel ℓ e
    rw [hpre]; exact List.mem_append_right _ he
  · intro j m hj hm hfl ℓ
    simp only [nodesOf, nodes_cons] at hj
    rcases getElem?_snoc hj with ⟨hj1, hj2⟩ | ⟨hj1, rfl⟩
    · intro hmem
      obtain ⟨pre, hpre⟩ := hlanes ℓ
      apply hr.hist j m hj2 hm hfl ℓ
      rw [hpre]; exact List.mem_append_right _ hmem
    · exact hhist hm hfl ℓ

/-! ### The judgment -/

/-- `m'` simulates `m`, with results related by `er`. -/
structure Sim2 (Hall : List ℕ) {α β : Type} (er : α → β) (m : FM α) (m' : HP β) : Prop where
  mono : ∀ h, (m' h).2.ok = true → h.ok = true
  run : ∀ Hf Ff t h, Rel Hall Hf Ff t h → (m' h).2.ok = true →
    er (m t).1 = (m' h).1 ∧ Rel Hall Hf Ff (m t).2 (m' h).2

namespace Sim2

variable {Hall : List ℕ} {α β γ δ : Type}

theorem pure {er : α → β} {a : α} {b : β} (h : er a = b) :
    Sim2 Hall er (Pure.pure a) (Pure.pure b) :=
  ⟨fun _ hh => hh, fun _ _ _ _ hr _ => ⟨h, hr⟩⟩

theorem HP.bind_apply {α β : Type} (m : HP α) (f : α → HP β) (s : HState) :
    (m >>= f) s = f (m s).1 (m s).2 := by
  show (match m s with | (a, s') => f a s') = _
  cases m s; rfl

theorem bind {er : α → β} {er' : γ → δ} (hs : Function.Surjective er) {m : FM α} {m' : HP β}
    {f : α → FM γ} {f' : β → HP δ} (hm : Sim2 Hall er m m')
    (hf : ∀ a, Sim2 Hall er' (f a) (f' (er a))) : Sim2 Hall er' (m >>= f) (m' >>= f') := by
  have hok1 : ∀ h, (f' (m' h).1 (m' h).2).2.ok = true → (m' h).2.ok = true := by
    intro h hok
    obtain ⟨a, ha⟩ := hs (m' h).1
    rw [← ha] at hok
    exact (hf a).mono _ hok
  refine ⟨fun h hok => ?_, fun Hf Ff t h hr hok => ?_⟩
  · rw [HP.bind_apply] at hok
    exact hm.mono h (hok1 h hok)
  · rw [HP.bind_apply] at hok ⊢
    obtain ⟨e1, r1⟩ := hm.run Hf Ff t h hr (hok1 h hok)
    rw [FM.bind_apply, ← e1]
    rw [← e1] at hok
    exact (hf (m t).1).run Hf Ff _ _ r1 hok

theorem bindN {er' : γ → δ} {m : FM ℕ} {m' : HP ℕ} {f : ℕ → FM γ} {f' : ℕ → HP δ}
    (hm : Sim2 Hall id m m') (hf : ∀ a, Sim2 Hall er' (f a) (f' a)) :
    Sim2 Hall er' (m >>= f) (m' >>= f') :=
  bind Function.surjective_id hm hf

theorem congr_er {er er' : α → β} {m : FM α} {m' : HP β} (h : Sim2 Hall er m m')
    (he : er = er') : Sim2 Hall er' m m' := he ▸ h

end Sim2


/-! ### Primitives -/

section Prims

variable {Hall : List ℕ}

theorem idxOf?_snoc_ne {l : List NatNode} {n m : NatNode} (h : m ≠ n) :
    (l ++ [n]).idxOf? m = l.idxOf? m := by
  rw [idxOf?_append_singleton]
  by_cases hm : m ∈ l
  · simp [hm]
  · simp [hm, h, List.idxOf?_eq_none_iff.mpr hm]

theorem idxOf?_snoc_new {l : List NatNode} {n : NatNode} (h : n ∉ l) :
    (l ++ [n]).idxOf? n = some l.length := by
  rw [idxOf?_append_singleton]; simp [h]

theorem getElem?_snoc_of {l : List NatNode} {n m : NatNode} {j : ℕ} (h : l[j]? = some m) :
    (l ++ [n])[j]? = some m := by
  rw [List.getElem?_append_left (getElem?_lt h)]; exact h

/-- The table of a fast state after appending a node that is not tabled. -/
theorem table_plain {t : FState} {n : NatNode} (hn : tabled n = false)
    (ht : ∀ m, tabled m = true → t.table.find m = (nodesOf t).idxOf? m) :
    ∀ m, tabled m = true → t.table.find m = (nodesOf t ++ [n]).idxOf? m := by
  intro m hm
  rw [idxOf?_snoc_ne (by rintro rfl; simp_all), ht m hm]

/-- The table of a fast state after inserting a new tabled node. -/
theorem table_insert {t : FState} {n : NatNode} (hn : tabled n = true) (hnew : n ∉ nodesOf t)
    (ht : ∀ m, tabled m = true → t.table.find m = (nodesOf t).idxOf? m)
    (hlen : t.len = t.rev.length) :
    ∀ m, tabled m = true → (t.table.insert n t.len).find m = (nodesOf t ++ [n]).idxOf? m := by
  intro m hm
  rw [Table.find_insert _ hn _ hm]
  by_cases hmn : m = n
  · subst hmn
    simp only [↓reduceIte, idxOf?_snoc_new hnew, hlen, nodesOf, List.length_reverse]
  · simp only [hmn, ↓reduceIte, idxOf?_snoc_ne hmn, ht m hm]

theorem countKind_cons (κ : NodeKind) (n : NatNode) (l : List NatNode) :
    countKind κ (n :: l) = countKind κ l + (if nodeKind n = κ then 1 else 0) := by
  simp [countKind, List.countP_cons]

theorem fresh_sim2 : Sim2 Hall id NodeCheck.fresh fresh := by
  refine ⟨fun h hok => ?_, fun Hf Ff t h hr hok => ?_⟩
  · simp only [fresh, force_eq] at hok; exact (create_eq hok).2.1
  · simp only [fresh, force_eq] at hok ⊢
    obtain ⟨-, -, hlim, he⟩ := create_eq hok
    rw [he]
    refine ⟨by simp [NodeCheck.fresh, hr.len], ?_⟩
    have hk : 5 * h.next + 2 = nodeKey (.var t.next) := by simp [nodeKey, hr.next]
    rw [hk, hr.next]
    exact hr.append (.var t.next) (t.next + 1) t.table _ _ _ _ _ _ hlim
      (table_plain rfl hr.table) (by simp [tabled]) (by simp [isOp])
      (by simp [countKind_cons, nodeKind, hr.adds]) (by simp [countKind_cons, nodeKind, hr.muls])
      (fun c => by rw [idxOf?_snoc_ne (by simp), hr.consts])
      (fun e he => by obtain ⟨m, h1, h2, h3⟩ := hr.hot e he; exact ⟨m, getElem?_snoc_of h1, h2, h3⟩)
      (fun ℓ => ⟨[], rfl⟩) (by simp [isOp]) hr.sorted

theorem callPower_sim2 (P Q R : ℕ) :
    Sim2 Hall toL (NodeCheck.callPower P Q R) (callPower P Q R) := by
  refine ⟨fun h hok => ?_, fun Hf Ff t h hr hok => ?_⟩
  · simp only [callPower, force_eq] at hok; exact (create_eq hok).2.1
  · simp only [callPower, force_eq] at hok ⊢
    obtain ⟨-, -, hlim, he⟩ := create_eq hok
    rw [he]
    refine ⟨by simp [NodeCheck.callPower, toL, hr.len], ?_⟩
    have hk : 0 = nodeKey (.call P Q R t.next) := rfl
    rw [hk, hr.next]
    exact hr.append (.call P Q R t.next) (t.next + powerWitnesses) t.table _ _ _ _ _ _ hlim
      (table_plain rfl hr.table) (by simp [tabled]) (by simp [isOp])
      (by simp [countKind_cons, nodeKind, hr.adds]) (by simp [countKind_cons, nodeKind, hr.muls])
      (fun c => by rw [idxOf?_snoc_ne (by simp), hr.consts])
      (fun e he => by obtain ⟨m, h1, h2, h3⟩ := hr.hot e he; exact ⟨m, getElem?_snoc_of h1, h2, h3⟩)
      (fun ℓ => ⟨[], rfl⟩) (by simp [isOp]) hr.sorted

theorem constant_sim2 (c : ℤ) : Sim2 Hall id (NodeCheck.constant c) (constant c) := by
  refine ⟨fun h hok => ?_, fun Hf Ff t h hr hok => ?_⟩
  · unfold constant at hok
    cases hc : constFind (lintKey c) h.consts with
    | some j => rw [hc] at hok; exact hok
    | none => rw [hc] at hok; exact (create_eq hok).2.1
  · have hf := hr.table (.const c) rfl
    rw [← hr.consts c] at hf
    unfold constant at hok ⊢
    unfold NodeCheck.constant NodeCheck.node
    cases hc : constFind (lintKey c) h.consts with
    | some j =>
      rw [hc] at hok hf
      rw [hf]
      exact ⟨rfl, hr⟩
    | none =>
      rw [hc] at hok hf
      rw [hf]
      dsimp only at hok ⊢
      obtain ⟨-, -, hlim, he⟩ := create_eq hok
      rw [he]
      have hnew : NatNode.const c ∉ nodesOf t := by
        rw [← List.idxOf?_eq_none_iff, ← hr.consts c, hc]
      refine ⟨by simp [hr.len], ?_⟩
      have hk : 5 * lintKey c + 1 = nodeKey (.const c) := by simp [nodeKey, lintKey_eq]
      rw [hk, hr.next]
      refine hr.append (.const c) t.next _ _ _ _ _ _ _ hlim
        (table_insert rfl hnew hr.table hr.lenRev) (fun _ => hnew) (by simp [isOp])
        (by simp [countKind_cons, nodeKind, hr.adds]) (by simp [countKind_cons, nodeKind, hr.muls])
        (fun c' => ?_)
        (fun e he => by obtain ⟨m, h1, h2, h3⟩ := hr.hot e he; exact ⟨m, getElem?_snoc_of h1, h2, h3⟩)
        (fun ℓ => ⟨[], rfl⟩) (by simp [isOp]) hr.sorted
      rw [constFind_cons]
      by_cases hcc : lintKey c = lintKey c'
      · have : c = c' := intKey_inj (by rw [← lintKey_eq]; exact hcc)
        subst this
        rw [ite_cond_eq_true _ _ (eq_self _), idxOf?_snoc_new hnew, hr.len, hr.lenRev]; simp [nodesOf]
      · have : NatNode.const c' ≠ .const c := by
          intro h'; injection h' with h'; exact hcc (by rw [h'])
        rw [ite_cond_eq_false _ _ (eq_false hcc), idxOf?_snoc_ne this, hr.consts]

theorem max_bif (a b : ℕ) : (bif a.blt b then b else a) = max a b := by
  by_cases hab : a < b
  · have : a.blt b = true := by simpa using hab
    rw [this]; simp only [Bool.cond_true]; omega
  · have : a.blt b = false := Bool.eq_false_iff.mpr (fun h => hab (by simpa using h))
    rw [this]; simp only [Bool.cond_false]; omega

/-- Changing the codes and shrinking the hot list preserves the relation. -/
theorem Rel.codes_hot {Hall Hf : List ℕ} {Ff : ℕ → List ℕ} {t : FState} {h : HState}
    (hr : Rel Hall Hf Ff t h) (cs : List ℕ) (hot' : List (ℕ × ℕ)) (hh : ∀ e ∈ hot', e ∈ h.hot) :
    Rel Hall Hf Ff t { h with codes := cs, hot := hot' } :=
  ⟨hr.len, hr.next, hr.lenRev, hr.table, hr.nodup, hr.child, hr.adds, hr.muls, hr.consts,
    fun e he => hr.hot e (hh e he), hr.win, hr.lim, hr.hubs, hr.hubsLim, hr.laneNodup,
    hr.laneLabel, hr.hist, hr.sorted⟩

theorem getElem?_nodes_rev {t : FState} {j : ℕ} {n : NatNode} (hlen : t.len = t.rev.length)
    (h : (nodesOf t)[j]? = some n) : t.rev[t.len - 1 - j]? = some n := by
  have hj := getElem?_lt h
  simp only [nodesOf, List.length_reverse] at hj h
  rw [List.getElem?_reverse hj] at h
  rw [hlen]; exact h

theorem flagOf_of_label {Hall : List ℕ} {y ℓ : ℕ} (hℓ : ℓ < 8) (h : 8 * y + ℓ ∈ Hall) :
    flagOf Hall y = true := by
  simp only [flagOf, decide_eq_true_eq, List.mem_map]
  exact ⟨_, h, by omega⟩

/-- The addition or multiplication node `n = op(a, b)`. -/
theorem nodeOp_sim2 {op a b : ℕ} {n : NatNode}
    (hn : (n = .add a b ∧ op = 0) ∨ (n = .mul a b ∧ op = 1)) :
    Sim2 Hall id (NodeCheck.node n) (nodeOp op a b) := by
  have hkey : opKey op a b = nodeKey n := by
    rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact opKey_add a b
    · exact opKey_mul a b
  have hop : isOp n = true := by rcases hn with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  have htab : tabled n = true := tabled_of_isOp hop
  have hy : youngest n = max a b := by rcases hn with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  have hcnt : ∀ (l : List NatNode) (x y : ℕ), x = countKind .add l → y = countKind .mul l →
      (bif Nat.beq op 0 then x + 1 else x) = countKind .add (n :: l) ∧
      (bif Nat.beq op 0 then y else y + 1) = countKind .mul (n :: l) := by
    intro l x y hx' hy'
    rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [countKind_cons, nodeKind, hx', hy']
  -- the creation of the node, from the facts that it is new and its children are older
  have hcreate : ∀ Hf Ff t h (hr : Rel Hall Hf Ff t h) (cs : List ℕ) (c hi : Bool)
      (lanes' : List (List ℕ)), (createOp op (opKey op a b) c hi cs lanes' h).ok = true →
      n ∉ nodesOf t → max a b < t.len →
      (∀ ℓ, ∃ pre, remL Ff h ℓ = pre ++ (lanes'.getD ℓ [] ++ Ff ℓ)) →
      (flagOf Hall (max a b) = true → ∀ ℓ, max a b * laneBase + nodeKey n ∉ lanes'.getD ℓ [] ++ Ff ℓ) →
      NodeCheck.node n t = (t.len, ⟨t.next, t.table.insert n t.len, t.len + 1, n :: t.rev⟩) ∧
      Rel Hall Hf Ff ⟨t.next, t.table.insert n t.len, t.len + 1, n :: t.rev⟩
        (createOp op (opKey op a b) c hi cs lanes' h) := by
    intro Hf Ff t h hr cs c hi lanes' hok hnew hlt hlanes hhist
    have hfind : t.table.find n = none := by
      rw [hr.table n htab, List.idxOf?_eq_none_iff]; exact hnew
    refine ⟨by unfold NodeCheck.node; rw [hfind], ?_⟩
    simp only [createOp, force_eq] at hok ⊢
    obtain ⟨-, -, hlim, he⟩ := create_eq hok
    rw [he, hkey, hr.next]
    obtain ⟨ha, hm⟩ := hcnt t.rev h.adds h.muls hr.adds hr.muls
    refine hr.append n t.next _ _ _ _ _ _ _ hlim (table_insert htab hnew hr.table hr.lenRev)
      (fun _ => hnew) (fun _ => by rw [hy]; exact hlt) ha hm
      (fun c' => by rw [idxOf?_snoc_ne (by rintro rfl; simp [isOp] at hop), hr.consts])
      (fun e he => ?_) hlanes (fun _ hf => by rw [hy] at hf ⊢; exact hhist hf) hr.sorted
    cases hi
    · obtain ⟨m, h1, h2, h3⟩ := hr.hot e he; exact ⟨m, getElem?_snoc_of h1, h2, h3⟩
    · rcases List.mem_cons.mp he with rfl | he
      · refine ⟨n, ?_, hop, rfl⟩
        simp only [hr.len, hr.lenRev]
        have : t.rev.length = (nodesOf t).length := by simp [nodesOf]
        rw [this, List.getElem?_append_right (le_refl _)]; simp
      · obtain ⟨m, h1, h2, h3⟩ := hr.hot e he; exact ⟨m, getElem?_snoc_of h1, h2, h3⟩
  have hcok : ∀ {k : ℕ} {c hi : Bool} {cs : List ℕ} {lanes' : List (List ℕ)} {h : HState},
      (createOp op k c hi cs lanes' h).ok = true → c = true ∧ h.ok = true := by
    intro k c hi cs lanes' h hok
    simp only [createOp, force_eq] at hok
    obtain ⟨h1, h2, -⟩ := create_eq hok
    exact ⟨h1, h2⟩
  refine ⟨fun h hok => ?_, fun Hf Ff t h hr hok => ?_⟩
  · unfold nodeOp at hok
    cases hc : h.codes with
    | nil => rw [hc] at hok; exact absurd hok (by simp [HState.fail])
    | cons c cs =>
      rw [hc] at hok
      simp only at hok
      cases hk1 : Nat.beq (c % 8) 1
      · rw [hk1] at hok
        simp only [Bool.cond_false] at hok
        cases hk0 : Nat.beq (c % 8) 0
        · rw [hk0] at hok
          simp only [Bool.cond_false] at hok
          revert hok
          cases lanePop (c % 8 - 2) ((bif a.blt b then b else a) * laneBase + opKey op a b) h.lanes
          intro hok
          exact (hcok hok).2
        · rw [hk0] at hok
          exact (hcok hok).2
      · rw [hk1] at hok
        simp only [Bool.cond_true] at hok
        revert hok
        cases hotTake (opKey op a b) h.hot with
        | none => simp
        | some p => intro hok; exact hok
  · unfold nodeOp at hok ⊢
    cases hc : h.codes with
    | nil => rw [hc] at hok; exact absurd hok (by simp [HState.fail])
    | cons c cs =>
      rw [hc] at hok
      simp only [hc] at hok ⊢
      rw [max_bif] at hok ⊢
      cases hk1 : Nat.beq (c % 8) 1
      · rw [hk1] at hok
        simp only [Bool.cond_false] at hok ⊢
        cases hk0 : Nat.beq (c % 8) 0
        · -- a far miss
          rw [hk0] at hok
          simp only [Bool.cond_false] at hok ⊢
          revert hok
          cases hp : lanePop (c % 8 - 2) (max a b * laneBase + opKey op a b) h.lanes with
          | mk bb lanes' =>
          intro hok
          simp only at hok ⊢
          have hck := (hcok hok).1
          simp only [Bool.and_eq_true, Nat.blt_eq] at hck
          obtain ⟨⟨hylt, hklt⟩, rfl⟩ := hck
          obtain ⟨hp1, hp2⟩ := lanePop_spec hp
          set ℓ := c % 8 - 2
          set e := max a b * laneBase + opKey op a b
          have hrem : remL Ff h ℓ = e :: remL Ff { h with lanes := lanes' } ℓ := by
            simp only [remL]; rw [hp1]; rfl
          have hrem' : ∀ ℓ', ℓ' ≠ ℓ → remL Ff { h with lanes := lanes' } ℓ' = remL Ff h ℓ' := by
            intro ℓ' hne; simp only [remL]; rw [hp2 ℓ' hne]
          have he_div : e / laneBase = max a b := by
            simp only [e]
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide : 0 < laneBase),
              Nat.div_eq_of_lt hklt, Nat.zero_add]
          obtain ⟨hℓ8, hlab⟩ := hr.laneLabel ℓ e (by rw [hrem]; exact List.mem_cons_self)
          rw [he_div] at hlab
          have hflag : flagOf Hall (max a b) = true := flagOf_of_label hℓ8 hlab
          have hnew : n ∉ nodesOf t := by
            intro hmem
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
            apply hr.hist j n hj hop (by rw [hy]; exact hflag) ℓ
            rw [hy, ← hkey, hrem]; exact List.mem_cons_self
          have hylt' : max a b < t.len := by rw [← hr.len]; exact hylt
          obtain ⟨e1, e2⟩ := hcreate Hf Ff t h hr cs _ _ lanes' hok hnew hylt'
            (fun ℓ' => by
              by_cases hne : ℓ' = ℓ
              · rw [hne]; exact ⟨[e], by rw [hrem]; rfl⟩
              · exact ⟨[], by rw [← hrem' ℓ' hne]; rfl⟩)
            (fun _ ℓ' hmem => by
              rw [← hkey] at hmem
              by_cases hne : ℓ' = ℓ
              · rw [hne] at hmem
                have hnd := hr.laneNodup ℓ
                rw [hrem] at hnd
                exact (List.nodup_cons.mp hnd).1 hmem
              · have hmem' : e ∈ remL Ff h ℓ' := by rw [← hrem' ℓ' hne]; exact hmem
                obtain ⟨hℓ8', hlab'⟩ := hr.laneLabel ℓ' e hmem'
                rw [he_div] at hlab'
                have := hubSorted_eq hr.sorted hlab hlab' (by omega)
                omega)
          rw [e1]
          exact ⟨by simp [hr.len], e2⟩
        · -- a local miss
          rw [hk0] at hok
          simp only [Bool.cond_true] at hok ⊢
          have hck := (hcok hok).1
          simp only [Bool.and_eq_true, Nat.blt_eq] at hck
          obtain ⟨hylt, hscan⟩ := hck
          obtain ⟨hd, hkeys, hflag⟩ := scan_spec hr.win hscan
          have hylt' : max a b < t.len := by rw [← hr.len]; exact hylt
          have hnew : n ∉ nodesOf t := by
            intro hmem
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
            have hjl := getElem?_lt hj
            simp only [nodesOf, List.length_reverse, ← hr.lenRev] at hjl
            by_cases hjy : max a b < j
            · apply hkeys (t.len - 1 - j) (by rw [hr.len]; omega) n
                (getElem?_nodes_rev hr.lenRev hj)
              exact hkey.symm
            · have := hr.child j n hj hop
              rw [hy] at this; omega
          obtain ⟨e1, e2⟩ := hcreate Hf Ff t h hr cs _ _ h.lanes hok hnew hylt'
            (fun ℓ => ⟨[], rfl⟩)
            (fun hf => by
              rw [show t.rev.length - 1 - (h.len - 1 - max a b) = max a b by
                rw [← hr.lenRev, hr.len]; omega] at hflag
              rw [hflag] at hf; exact absurd hf (by simp))
          rw [e1]
          exact ⟨by simp [hr.len], e2⟩
      · -- a hit
        rw [hk1] at hok
        simp only [Bool.cond_true] at hok ⊢
        revert hok
        cases hp : hotTake (opKey op a b) h.hot with
        | none => simp
        | some p =>
          obtain ⟨j, rest⟩ := p
          intro _
          simp only
          obtain ⟨hp1, hp2⟩ := hotTake_spec hp
          obtain ⟨m, hm1, hm2, hm3⟩ := hr.hot _ hp1
          have hmn : m = n := key_inj (isCall_of_tabled (tabled_of_isOp hm2))
            (isCall_of_tabled htab) (by rw [hm3, hkey])
          subst hmn
          have hidx : (nodesOf t).idxOf? m = some j := by
            obtain ⟨i, hi⟩ : ∃ i, (nodesOf t).idxOf? m = some i := Option.isSome_iff_exists.mp
              (List.isSome_idxOf?.mpr (List.mem_of_getElem? hm1))
            have hi' : (nodesOf t)[i]? = some m := by
              obtain ⟨hlt, hget, -⟩ := List.idxOf?_eq_some_iff.mp hi
              rw [List.getElem?_eq_getElem hlt, hget]
            rw [hi, hr.nodup i j m hi' hm1 htab]
          have hfind : t.table.find m = some j := by rw [hr.table m htab, hidx]
          refine ⟨by unfold NodeCheck.node; rw [hfind]; rfl, ?_⟩
          unfold NodeCheck.node; rw [hfind]
          refine hr.codes_hot cs _ (fun e he => ?_)
          cases hb : Nat.beq (c / 8) 0
          · rw [hb] at he; exact hp2 e he
          · rw [hb] at he
            rcases List.mem_cons.mp he with rfl | he
            · exact hp1
            · exact hp2 e he

end Prims

end ZInQ.Compiler.NodeSkeleton
