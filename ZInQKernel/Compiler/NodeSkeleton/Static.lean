import ZInQKernel.Compiler.NodeSkeleton.Core

/-!
# The global checks of the hub list and the far lanes (no Mathlib)

The pinned data of the chunks: for chunk `c`, its hubs `hubsData[c]` (entries `8 · index +
label`) and its far lanes `lanesData[c]` (entries `y · 2^42 + key`). The global hub list is
`hubsAll`, lane `ℓ` over all chunks is `laneAll ℓ`.

* `sortedHubsB`: the hub indices are strictly increasing (`hubSorted_of`);
* `laneOKB`: lane `ℓ` sorted by a natural merge sort is strictly increasing (so the lane has
  no repeated entry) and every entry `e` has the hub `8 · (e / 2^42) + ℓ`, with `ℓ < 8`
  (`laneNodup_of`, `laneLabel_of`).
-/

namespace ZInQ.Compiler.NodeSkeleton

/-! ### Sorting -/

/-- Merge two lists, with fuel (when the fuel runs out, the lists are concatenated). -/
def mergeF : Nat → List Nat → List Nat → List Nat :=
  Nat.rec (fun xs ys => xs ++ ys) (fun _ ih xs ys =>
    List.casesOn (motive := fun _ => List Nat) xs ys (fun x xs' =>
      List.casesOn (motive := fun _ => List Nat) ys (x :: xs') (fun y ys' =>
        cond (Nat.blt x y) (x :: ih xs' (y :: ys')) (y :: ih (x :: xs') ys'))))

/-- Merge consecutive pairs of lists. -/
def mergePairs : List (List Nat) → List (List Nat)
  | a :: b :: rest => mergeF (a.length + b.length) a b :: mergePairs rest
  | l => l

/-- Merge a list of lists into one, with fuel. -/
def mergeAll : Nat → List (List Nat) → List Nat
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | n + 1, ls => mergeAll n (mergePairs ls)

/-- The strictly increasing runs of a list: the current run (reversed) and the finished runs
(reversed). -/
def runsAux : List Nat → List Nat → List (List Nat) → List (List Nat)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | x :: l, [], acc => runsAux l [x] acc
  | x :: l, y :: cur, acc =>
    bif Nat.blt y x then runsAux l (x :: y :: cur) acc else runsAux l [x] ((y :: cur).reverse :: acc)

/-- Natural merge sort. -/
def msortNat (l : List Nat) : List Nat := mergeAll 40 (runsAux l [] [])

/-- Strictly increasing. -/
def strictIncB : List Nat → Bool
  | a :: b :: l => Nat.blt a b && strictIncB (b :: l)
  | _ => true

theorem mergeF_perm : ∀ (n : Nat) (xs ys : List Nat), (mergeF n xs ys).Perm (xs ++ ys)
  | 0, xs, ys => List.Perm.refl _
  | n + 1, [], ys => List.Perm.refl _
  | n + 1, x :: xs, [] => by simp [mergeF]
  | n + 1, x :: xs, y :: ys => by
    show (cond (Nat.blt x y) (x :: mergeF n xs (y :: ys)) (y :: mergeF n (x :: xs) ys)).Perm _
    cases Nat.blt x y
    · simp only [Bool.cond_false]
      have := mergeF_perm n (x :: xs) ys
      refine (List.Perm.cons y this).trans ?_
      exact (List.perm_middle (a := y) (l₁ := x :: xs) (l₂ := ys)).symm
    · simp only [Bool.cond_true, List.cons_append]
      exact List.Perm.cons x (mergeF_perm n xs (y :: ys))

theorem mergePairs_perm : ∀ ls : List (List Nat), (mergePairs ls).flatten.Perm ls.flatten
  | a :: b :: rest => by
    simp only [mergePairs, List.flatten_cons]
    rw [← List.append_assoc]
    exact List.Perm.append (mergeF_perm _ a b) (mergePairs_perm rest)
  | [] => List.Perm.refl _
  | [a] => List.Perm.refl _

theorem mergeAll_perm : ∀ (n : Nat) (ls : List (List Nat)), (mergeAll n ls).Perm ls.flatten
  | 0, ls => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [a] => by simp [mergeAll]
  | n + 1, a :: b :: rest => by
    show (mergeAll n (mergePairs (a :: b :: rest))).Perm _
    exact (mergeAll_perm n _).trans (mergePairs_perm _)

theorem runsAux_flatten : ∀ (l cur : List Nat) (acc : List (List Nat)),
    (runsAux l cur acc).flatten = acc.reverse.flatten ++ cur.reverse ++ l
  | [], cur, acc => by simp [runsAux]
  | x :: l, [], acc => by simp [runsAux, runsAux_flatten l [x] acc]
  | x :: l, y :: cur, acc => by
    show (cond (Nat.blt y x) (runsAux l (x :: y :: cur) acc)
      (runsAux l [x] ((y :: cur).reverse :: acc))).flatten = _
    cases Nat.blt y x
    · simp [runsAux_flatten l [x]]
    · simp [runsAux_flatten l (x :: y :: cur)]

theorem msortNat_perm (l : List Nat) : (msortNat l).Perm l := by
  unfold msortNat
  refine (mergeAll_perm _ _).trans ?_
  rw [runsAux_flatten]; simp

theorem strictIncB_pairwise : ∀ {l : List Nat}, strictIncB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictIncB, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := strictIncB_pairwise h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem nodup_of_strictIncB {l : List Nat} (h : strictIncB (msortNat l) = true) : l.Nodup := by
  have hs := strictIncB_pairwise h
  have hn : (msortNat l).Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  exact (msortNat_perm l).nodup_iff.mp hn

/-! ### Hubs -/

/-- Strictly increasing hub indices. -/
def sortedHubsB : List Nat → Bool
  | a :: b :: l => Nat.blt (a / 8) (b / 8) && sortedHubsB (b :: l)
  | _ => true

theorem sortedHubsB_pairwise : ∀ {l : List Nat}, sortedHubsB l = true →
    l.Pairwise fun a b => a / 8 < b / 8
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [sortedHubsB, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := sortedHubsB_pairwise h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- Every entry `e` of the sorted list `l` has the hub `8 · (e / 2^42) + ℓ` in the hub list
`H` (walked in step, both sorted), with fuel. -/
def labelsGo (ℓ : Nat) : Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => true
  | _ + 1, _ :: _, [] => false
  | n + 1, e :: l, h :: H =>
    bif Nat.blt (h / 8) (e / laneBase) then labelsGo ℓ n (e :: l) H
    else Nat.beq h (8 * (e / laneBase) + ℓ) && labelsGo ℓ n l (h :: H)

/-- The labels check. -/
def labelsB (ℓ : Nat) (l H : List Nat) : Bool := labelsGo ℓ (l.length + H.length + 1) l H

theorem labelsGo_sound (ℓ : Nat) : ∀ {n : Nat} {l H : List Nat}, labelsGo ℓ n l H = true →
    ∀ e ∈ l, 8 * (e / laneBase) + ℓ ∈ H
  | 0, _, _, hc, _, _ => by simp [labelsGo] at hc
  | _ + 1, [], _, _, e, he => by simp at he
  | _ + 1, _ :: _, [], hc, _, _ => by simp [labelsGo] at hc
  | n + 1, e :: l, h :: H, hc, x, hx => by
    simp only [labelsGo] at hc
    cases hb : Nat.blt (h / 8) (e / laneBase)
    · rw [hb] at hc
      simp only [Bool.cond_false, Bool.and_eq_true, Nat.beq_eq] at hc
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [← hc.1]; exact List.mem_cons_self
      · exact labelsGo_sound ℓ hc.2 x hx
    · rw [hb] at hc
      simp only [Bool.cond_true] at hc
      exact List.mem_cons_of_mem _ (labelsGo_sound ℓ hc x hx)

theorem labelsB_sound (ℓ : Nat) {l H : List Nat} (h : labelsB ℓ l H = true) :
    ∀ e ∈ l, 8 * (e / laneBase) + ℓ ∈ H := labelsGo_sound ℓ h

/-! ### The data -/

/-- The global hub list. -/
def hubsAll (hubsData : List (List Nat)) : List Nat := hubsData.flatten

/-- Lane `ℓ` over all chunks. -/
def laneAll (lanesData : List (List (List Nat))) (ℓ : Nat) : List Nat :=
  (lanesData.map fun ls => ls.getD ℓ []).flatten

/-- The check of lane `ℓ`. -/
def laneOKB (hubsData : List (List Nat)) (lanesData : List (List (List Nat))) (ℓ : Nat) : Bool :=
  let s := msortNat (laneAll lanesData ℓ)
  Nat.blt ℓ 8 && strictIncB s && labelsB ℓ s (hubsAll hubsData)

theorem hubSorted_of {hubsData : List (List Nat)} (h : sortedHubsB (hubsAll hubsData) = true) :
    (hubsAll hubsData).Pairwise fun a b => a / 8 < b / 8 := sortedHubsB_pairwise h

theorem laneNodup_of {hubsData : List (List Nat)} {lanesData : List (List (List Nat))} {ℓ : Nat}
    (h : laneOKB hubsData lanesData ℓ = true) : (laneAll lanesData ℓ).Nodup := by
  simp only [laneOKB, Bool.and_eq_true] at h
  exact nodup_of_strictIncB h.1.2

theorem laneLabel_of {hubsData : List (List Nat)} {lanesData : List (List (List Nat))} {ℓ : Nat}
    (h : laneOKB hubsData lanesData ℓ = true) :
    ∀ e ∈ laneAll lanesData ℓ, ℓ < 8 ∧ 8 * (e / laneBase) + ℓ ∈ hubsAll hubsData := by
  simp only [laneOKB, Bool.and_eq_true, Nat.blt_eq] at h
  intro e he
  exact ⟨h.1.1, labelsB_sound ℓ h.2 e ((msortNat_perm _).mem_iff.mpr he)⟩

/-! ### Hub bounds -/

/-- The hub bound of every chunk: the hubs of the later chunks lie at or beyond its `lim`
(checked on the first later hub, the list being sorted). -/
def hubsLimB : List Nat → List (List Nat) → Bool
  | lim :: lims, _ :: hs =>
    (match hs.flatten with
      | [] => true
      | x :: _ => Nat.ble lim (x / 8)) && hubsLimB lims hs
  | _, _ => true

theorem pairwise_head_le {x : Nat} {l : List Nat} (h : (x :: l).Pairwise fun a b => a / 8 < b / 8) :
    ∀ e ∈ x :: l, x / 8 ≤ e / 8 := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (List.rel_of_pairwise_cons h he)

theorem hubsLimB_sound : ∀ {lims : List Nat} {hs : List (List Nat)},
    hs.flatten.Pairwise (fun a b => a / 8 < b / 8) → hubsLimB lims hs = true →
      ∀ c, c < lims.length → ∀ e ∈ (hs.drop (c + 1)).flatten, lims.getD c 0 ≤ e / 8
  | [], _, _, _, c, hc, _, _ => by simp at hc
  | _ :: _, [], _, _, c, _, e, he => by simp at he
  | lim :: lims, h0 :: hs, hp, hb, c, hc, e, he => by
    simp only [hubsLimB, Bool.and_eq_true] at hb
    have hp' : hs.flatten.Pairwise (fun a b => a / 8 < b / 8) := by
      rw [List.flatten_cons] at hp; exact (List.pairwise_append.mp hp).2.1
    cases c with
    | zero =>
      simp only [List.drop_succ_cons, List.drop_zero] at he
      simp only [List.getD_cons_zero]
      cases hfl : hs.flatten with
      | nil => rw [hfl] at he; simp at he
      | cons x l =>
        rw [hfl] at he hp' hb
        simp only [Nat.ble_eq] at hb
        exact Nat.le_trans hb.1 (pairwise_head_le hp' e he)
    | succ c =>
      simp only [List.getD_cons_succ]
      exact hubsLimB_sound hp' hb.2 c (by simp at hc; omega) e (by simpa using he)

/-- The index of the first hub. -/
def firstHubGe (n : Nat) (hs : List (List Nat)) : Bool :=
  match hs.flatten with
  | [] => true
  | x :: _ => Nat.ble n (x / 8)

theorem firstHubGe_sound {n : Nat} {hs : List (List Nat)}
    (hp : hs.flatten.Pairwise (fun a b => a / 8 < b / 8)) (h : firstHubGe n hs = true) :
    ∀ e ∈ hs.flatten, n ≤ e / 8 := by
  unfold firstHubGe at h
  intro e he
  cases hfl : hs.flatten with
  | nil => rw [hfl] at he; simp at he
  | cons x l =>
    rw [hfl] at he hp h
    simp only [Nat.ble_eq] at h
    exact Nat.le_trans h (pairwise_head_le hp e he)

/-- Every chunk has at most `n` lanes. -/
def lanesLenB (n : Nat) (ls : List (List (List Nat))) : Bool := ls.all fun l => Nat.ble l.length n

theorem laneAll_nil {n : Nat} {ls : List (List (List Nat))} (h : lanesLenB n ls = true) {ℓ : Nat}
    (hℓ : n ≤ ℓ) : laneAll ls ℓ = [] := by
  unfold laneAll
  simp only [List.flatten_eq_nil_iff, List.mem_map]
  rintro _ ⟨l, hl, rfl⟩
  simp only [lanesLenB, List.all_eq_true, Nat.ble_eq] at h
  have := h l hl
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ ℓ)]

end ZInQ.Compiler.NodeSkeleton
