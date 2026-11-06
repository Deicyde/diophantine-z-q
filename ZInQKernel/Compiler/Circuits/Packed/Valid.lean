import ZInQKernel.Compiler.Circuits.Packed.Construction
import ZInQKernel.Compiler.Circuits.Builder

/-!
# Builder soundness for the packed-history construction

Every expression and formula handed out by the packed-history construction is valid, so the
polynomial of the compiled circuit is the compilation of the construction's formula
(`compiled_poly`). (Helper for `compiler/natural/formulas/hierarchical-calls.md` and
`compiler/natural/packed/register-machine-polynomial.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Packed

open Natural RM Syntax MvPolynomial

variable {T : ExPoly}

theorem getD_valid {L : List Ex} {d : Ex} {s : State} (hL : ∀ x ∈ L, x.Valid T s)
    (hd : d.Valid T s) (i : ℕ) : (L.getD i d).Valid T s := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hL _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hd

theorem getLastD_valid {L : List Ex} {d : Ex} {s : State} (hL : ∀ x ∈ L, x.Valid T s)
    (hd : d.Valid T s) : (L.getLastD d).Valid T s := by
  cases L using List.reverseRecOn with
  | nil => exact hd
  | append_singleton l e => simp only [List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, Option.getD_some]; exact hL e (by simp)

theorem lookupVW_valid {zero : Ex} {vw : List (ℕ × Ex × Ex)} {s : State}
    (hz : zero.Valid T s) (hvw : ∀ e ∈ vw, e.2.1.Valid T s ∧ e.2.2.Valid T s) (i : ℕ) :
    (lookupVW zero vw i).1.Valid T s ∧ (lookupVW zero vw i).2.Valid T s := by
  unfold lookupVW
  cases h : vw.find? (fun e => e.1 == i) with
  | none => exact ⟨hz, hz⟩
  | some v => exact hvw v (List.mem_of_find?_eq_some h)

theorem Triple.freshN {P : State → Prop} (hP : Mono P) (n : ℕ) :
    Triple P (freshN n) fun l s => ∀ h ∈ l, h.Valid T s := by
  induction n with
  | zero => exact Triple.pure _ fun _ _ h hh => absurd hh List.not_mem_nil
  | succ n ih =>
    refine Triple.bind hP (Triple.fresh (T := T) P) fun h => ?_
    refine Triple.bind (hP.and (Mono.valid T h)) (ih.pre fun s hs => hs.1) fun l => ?_
    exact Triple.pure _ fun s hs x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hs.1.2
      · exact hs.2 x hx

theorem Triple.appendM' {P : State → Prop} (hP : Mono P) {m₁ m₂ : NM (List NForm)}
    (h₁ : Triple P m₁ fun l s => ∀ φ ∈ l, φ.Valid T s)
    (h₂ : Triple P m₂ fun l s => ∀ φ ∈ l, φ.Valid T s) :
    Triple P (appendM m₁ m₂) fun l s => ∀ φ ∈ l, φ.Valid T s := by
  refine Triple.bind hP h₁ fun l₁ => ?_
  refine Triple.bind (hP.and (Mono.forall_mem l₁ fun φ => Mono.nvalid T φ))
    (h₂.pre fun s hs => hs.1) fun l₂ => ?_
  exact Triple.pure _ fun s hs φ hφ => by
    rcases List.mem_append.1 hφ with hφ | hφ
    · exact hs.1.2 φ hφ
    · exact hs.2 φ hφ

theorem Triple.seqConcat' {P : State → Prop} (hP : Mono P) :
    ∀ (ms : List (NM (List NForm))), (∀ m ∈ ms, Triple P m fun l s => ∀ φ ∈ l, φ.Valid T s) →
      Triple P (seqConcat ms) fun l s => ∀ φ ∈ l, φ.Valid T s
  | [], _ => Triple.pure _ fun _ _ _ hφ => absurd hφ List.not_mem_nil
  | m :: ms, h => Triple.appendM' hP (h m List.mem_cons_self)
      (Triple.seqConcat' hP ms fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))

theorem Triple.seqM' {P : State → Prop} (hP : Mono P) (ms : List (NM NForm))
    (h : ∀ m ∈ ms, Triple P m fun φ s => φ.Valid T s) :
    Triple P (Natural.seqM ms) fun l s => ∀ φ ∈ l, φ.Valid T s :=
  Triple.seqM hP (fun φ => Mono.nvalid T φ) ms h

/-- The validity of the handles of the packed construction. -/
def HV (T : ExPoly) (a : List Ex) (zero one q c K B T' F D : Ex) (R N S : List Ex) (s : State) :
    Prop :=
  (zero.Valid T s ∧ one.Valid T s ∧ q.Valid T s ∧ c.Valid T s ∧ K.Valid T s ∧ B.Valid T s ∧
    T'.Valid T s ∧ F.Valid T s ∧ D.Valid T s) ∧
  (∀ x ∈ a, x.Valid T s) ∧ (∀ x ∈ R, x.Valid T s) ∧ (∀ x ∈ N, x.Valid T s) ∧
    ∀ x ∈ S, x.Valid T s

theorem HV.mono {a : List Ex} {zero one q c K B T' F D : Ex} {R N S : List Ex} :
    Mono (HV T a zero one q c K B T' F D R N S) := fun _ _ hs h =>
  ⟨⟨h.1.1.mono T hs, h.1.2.1.mono T hs, h.1.2.2.1.mono T hs, h.1.2.2.2.1.mono T hs,
    h.1.2.2.2.2.1.mono T hs, h.1.2.2.2.2.2.1.mono T hs, h.1.2.2.2.2.2.2.1.mono T hs,
    h.1.2.2.2.2.2.2.2.1.mono T hs, h.1.2.2.2.2.2.2.2.2.mono T hs⟩,
    fun x hx => (h.2.1 x hx).mono T hs, fun x hx => (h.2.2.1 x hx).mono T hs,
    fun x hx => (h.2.2.2.1 x hx).mono T hs, fun x hx => (h.2.2.2.2 x hx).mono T hs⟩

section phases

variable {a : List Ex} {zero one q c K B T' F D : Ex} {R N S : List Ex}

local notation "HVP" => HV T a zero one q c K B T' F D R N S

theorem triple_items1 (p : Program) :
    Triple HVP (items1 p a zero q c K B T') fun l s => ∀ φ ∈ l, φ.Valid T s := by
  have hP : Mono HVP := HV.mono
  refine Triple.seqM' hP _ fun m hm => ?_
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_nil_iff, or_false] at hm
  rcases hm with (rfl | rfl | rfl | rfl | rfl) | ⟨ai, hai, rfl⟩
  · exact Triple.lt hP fun s hs => ⟨hs.1.1, hs.1.2.2.2.1⟩
  · exact Triple.bind hP (Triple.constant (T := T) _ 2) fun two =>
      Triple.power (hP.and (Mono.valid T two)) fun s hs => ⟨hs.1.1.2.2.2.2.1, hs.2, hs.1.1.2.2.2.1⟩
  · exact Triple.bind hP (Triple.scale hP 4 K fun s hs => hs.1.2.2.2.2.1) fun e =>
      Triple.pure _ fun s hs => by simp only [NForm.Valid]; exact ⟨hs.1.1.2.2.2.2.2.1, hs.2⟩
  · exact Triple.bind hP (Triple.constant (T := T) _ p.length) fun e =>
      Triple.lt (hP.and (Mono.valid T e)) fun s hs => ⟨hs.2, hs.1.1.2.2.2.2.2.1⟩
  · exact Triple.power hP fun s hs => ⟨hs.1.2.2.2.2.2.2.1, hs.1.2.2.2.2.2.1, hs.1.2.2.1⟩
  · exact Triple.lt hP fun s hs => ⟨hs.2.1 ai hai, hs.1.2.2.2.2.1⟩

theorem triple_items2 :
    Triple HVP (items2 zero one K B T' F D S) fun l s => ∀ φ ∈ l, φ.Valid T s := by
  have hP : Mono HVP := HV.mono
  refine Triple.seqM' hP _ fun m hm => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · refine Triple.bind hP (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e1 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.2.2.2.2.2.1, hs.1.2.2.2.2.2.2.2.1]
    refine Triple.bind (hP.and (Mono.valid T e1)) (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e2 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.2, hs.1.1.2.1]
    refine Triple.bind ((hP.and (Mono.valid T e1)).and (Mono.valid T e2))
      (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e3 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.1.2.2.2.2.2.1, hs.1.1.1.2.2.2.2.2.2.1]
    refine Triple.bind (((hP.and (Mono.valid T e1)).and (Mono.valid T e2)).and (Mono.valid T e3))
      (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e4 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.1.1.2.2.2.2.2.2.2.1, hs.2]
    exact Triple.pure _ fun s hs => by simp only [NForm.Valid]; exact ⟨hs.1.1.2, hs.2⟩
  · refine Triple.bind hP (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e1 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.2.2.2.2.2.2.2.2, hs.1.2.2.2.2.2.2.2.1]
    refine Triple.bind (hP.and (Mono.valid T e1)) (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e2 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.2.2.2.2.1, hs.1.1.2.2.2.2.2.2.2.1]
    exact Triple.pure _ fun s hs => by simp only [NForm.Valid]; exact ⟨hs.1.2, hs.2⟩
  · refine Triple.bind hP (Triple.addL (T := T) _ fun s hs x hx => hs.2.2.2.2 x hx) fun e1 => ?_
    exact Triple.pure _ fun s hs => by
      simp only [NForm.Valid]; exact ⟨hs.2, hs.1.1.2.2.2.2.2.2.2.1⟩
  · exact Triple.pure _ fun s hs => by
      simp only [NForm.Valid]
      exact ⟨getLastD_valid hs.2.2.2.2 hs.1.1, hs.1.2.2.2.2.2.2.1⟩

theorem triple_items3 :
    Triple HVP (items3 F S) fun l s => ∀ φ ∈ l, φ.Valid T s := by
  have hP : Mono HVP := HV.mono
  refine Triple.seqM' hP _ fun m hm => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  exact Triple.mask hP fun s hs => ⟨hs.2.2.2.2 x hx, hs.1.2.2.2.2.2.2.2.1⟩

theorem triple_items4 (r : ℕ) :
    Triple HVP (items4 r zero K D T' F R N) fun l s => ∀ φ ∈ l, φ.Valid T s := by
  have hP : Mono HVP := HV.mono
  refine Triple.seqConcat' hP _ fun m hm => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
  refine Triple.seqM' hP _ fun m hm => ?_
  have hR : ∀ s, HVP s → (R.getD j zero).Valid T s := fun s hs => getD_valid hs.2.2.1 hs.1.1 j
  have hN : ∀ s, HVP s → (N.getD j zero).Valid T s := fun s hs => getD_valid hs.2.2.2.1 hs.1.1 j
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact Triple.mask hP fun s hs => ⟨hR s hs, hs.1.2.2.2.2.2.2.2.2⟩
  · exact Triple.lt hP fun s hs => ⟨hR s hs, hs.1.2.2.2.2.2.2.1⟩
  · refine Triple.bind hP (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e1 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.2.2.2.2.1, hN s hs]
    refine Triple.bind (hP.and (Mono.valid T e1)) (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e2 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hR s hs.1, hs.1.1.2.2.2.2.2.2.2.2]
    refine Triple.bind ((hP.and (Mono.valid T e1)).and (Mono.valid T e2))
      (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e3 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.1.2.2.2.2.1, hs.1.1.1.2.2.2.2.2.2.2.1]
    exact Triple.bitAnd (((hP.and (Mono.valid T e1)).and (Mono.valid T e2)).and
      (Mono.valid T e3)) fun s hs => ⟨hs.1.1.2, hs.1.2, hs.2⟩

/-- Validity of the formulas and branch histories of the sub instructions. -/
theorem triple_subBranches (i : ℕ) (rest : Program) :
    Triple HVP (subBranches zero S N i rest) fun r s =>
      (∀ φ ∈ r.1, φ.Valid T s) ∧ ∀ e ∈ r.2, e.2.1.Valid T s ∧ e.2.2.Valid T s := by
  have hP : Mono HVP := HV.mono
  induction rest generalizing i with
  | nil => exact Triple.pure _ fun s _ => ⟨by simp, by simp⟩
  | cons ins rest ih =>
    cases ins with
    | dec j x y =>
      refine Triple.bind hP (Triple.fresh (T := T) _) fun V => ?_
      refine Triple.bind (hP.and (Mono.valid T V)) (Triple.fresh (T := T) _) fun W => ?_
      have hP2 := (hP.and (Mono.valid T V)).and (Mono.valid T W)
      refine Triple.bind hP2 (Triple.seqM' (T := T) hP2 _ fun m hm => ?_) fun fs => ?_
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl
        · exact Triple.bitAnd hP2 fun s hs => ⟨hs.1.2, getD_valid hs.1.1.2.2.2.2 hs.1.1.1.1 i,
            getD_valid hs.1.1.2.2.2.1 hs.1.1.1.1 j⟩
        · refine Triple.bind hP2 (Triple.addL (T := T) _ fun s hs z hz => ?_) fun e => ?_
          · simp at hz; rcases hz with rfl | rfl
            exacts [hs.1.2, hs.2]
          exact Triple.pure _ fun s hs => by
            simp only [NForm.Valid]
            exact ⟨getD_valid hs.1.1.1.2.2.2.2 hs.1.1.1.1.1 i, hs.2⟩
      have hP3 := hP2.and (Mono.forall_mem fs fun φ => Mono.nvalid T φ)
      refine Triple.bind hP3 ((ih (i + 1)).pre fun s hs => hs.1.1.1) fun rest' => ?_
      exact Triple.pure _ fun s hs => ⟨fun φ hφ => by
          rcases List.mem_append.1 hφ with hφ | hφ
          · exact hs.1.2 φ hφ
          · exact hs.2.1 φ hφ, fun e he => by
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨hs.1.1.1.2, hs.1.1.2⟩
          · exact hs.2.2 e he⟩
    | inc j x => exact ih (i + 1)
    | halt => exact ih (i + 1)

theorem triple_items67 (p : Program) (r : ℕ) (vw : List (ℕ × Ex × Ex)) :
    Triple (fun s => HVP s ∧ ∀ e ∈ vw, e.2.1.Valid T s ∧ e.2.2.Valid T s)
      (appendM (items6 p r a zero B R S vw) (items7 p zero one B S vw))
      fun l s => ∀ φ ∈ l, φ.Valid T s := by
  have hP : Mono fun s => HVP s ∧ ∀ e ∈ vw, e.2.1.Valid T s ∧ e.2.2.Valid T s :=
    HV.mono.and fun s s' hs h e he => ⟨(h e he).1.mono T hs, (h e he).2.mono T hs⟩
  have hlook : ∀ s, (HVP s ∧ ∀ e ∈ vw, e.2.1.Valid T s ∧ e.2.2.Valid T s) → ∀ i,
      (lookupVW zero vw i).1.Valid T s ∧ (lookupVW zero vw i).2.Valid T s :=
    fun s hs i => lookupVW_valid hs.1.1.1 hs.2 i
  refine Triple.appendM' hP (Triple.seqM' hP _ fun m hm => ?_) (Triple.seqM' hP _ fun m hm => ?_)
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
    unfold registerEq
    refine Triple.bind hP (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e1 => ?_
    · simp only [decHandles, List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact (hlook s hs i).1
    have hP1 := hP.and (Mono.valid T e1)
    refine Triple.bind hP1 (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e2 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.1.2.2.2.2.2.1, hs.2]
    have hP2 := hP1.and (Mono.valid T e2)
    refine Triple.bind hP2 (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e3 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [getD_valid hs.1.1.1.2.2.1 hs.1.1.1.1.1 j, hs.2]
    have hP3 := hP2.and (Mono.valid T e3)
    refine Triple.bind hP3 (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e4 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.1.1.1.2.2.2.2.2.1, getD_valid hs.1.1.1.1.2.2.1 hs.1.1.1.1.1.1 j]
    have hP4 := hP3.and (Mono.valid T e4)
    refine Triple.bind hP4 (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e5 => ?_
    · simp only [incHandles, List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact getD_valid hs.1.1.1.1.1.2.2.2.2 hs.1.1.1.1.1.1.1 i
    have hP5 := hP4.and (Mono.valid T e5)
    refine Triple.bind hP5 (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e6 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.1.1.1.1.1.2.2.2.2.2.1, hs.2]
    have hP6 := hP5.and (Mono.valid T e6)
    refine Triple.bind hP6 (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e7 => ?_
    · simp at hx; rcases hx with rfl | rfl | rfl
      · exact getD_valid hs.1.1.1.1.1.1.1.2.1 hs.1.1.1.1.1.1.1.1.1 j
      · exact hs.1.1.2
      · exact hs.2
    exact Triple.pure _ fun s hs => by simp only [NForm.Valid]; exact ⟨hs.1.1.1.1.2, hs.2⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hm
    unfold stateEq
    refine Triple.bind hP (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e1 => ?_
    · simp only [inHandles, List.mem_flatMap, List.mem_append] at hx
      obtain ⟨i', -, hx⟩ := hx
      rcases hx with (hx | hx) | hx <;> split_ifs at hx <;> simp at hx <;> rw [hx]
      · exact getD_valid hs.1.2.2.2.2 hs.1.1.1 i'
      · exact (hlook s hs i').1
      · exact (hlook s hs i').2
    have hP1 := hP.and (Mono.valid T e1)
    refine Triple.bind hP1 (Triple.mulL (T := T) _ fun s hs x hx => ?_) fun e2 => ?_
    · simp at hx; rcases hx with rfl | rfl
      exacts [hs.1.1.1.2.2.2.2.2.1, hs.2]
    have hP2 := hP1.and (Mono.valid T e2)
    refine Triple.bind hP2 (Triple.addL (T := T) _ fun s hs x hx => ?_) fun e3 => ?_
    · simp at hx; rcases hx with rfl | rfl
      · split_ifs
        · exact hs.1.1.1.1.2.1
        · exact hs.1.1.1.1.1
      · exact hs.2
    exact Triple.pure _ fun s hs => by
      simp only [NForm.Valid]
      exact ⟨getD_valid hs.1.1.1.1.2.2.2.2 hs.1.1.1.1.1.1 i, hs.2⟩

theorem triple_packedFormulas (p : Program) (r : ℕ) :
    Triple HVP (packedFormulas p r a zero one q c K B T' F D R N S)
      fun l s => ∀ φ ∈ l, φ.Valid T s := by
  have hP : Mono HVP := HV.mono
  unfold packedFormulas
  refine Triple.appendM' hP (triple_items1 p) (Triple.appendM' hP triple_items2
    (Triple.appendM' hP triple_items3 (Triple.appendM' hP (triple_items4 r) ?_)))
  refine Triple.bind hP (triple_subBranches 0 p) fun sb => ?_
  have hP' : Mono fun s => HVP s ∧ ((∀ φ ∈ sb.1, φ.Valid T s) ∧
      ∀ e ∈ sb.2, e.2.1.Valid T s ∧ e.2.2.Valid T s) :=
    hP.and ((Mono.forall_mem sb.1 fun φ => Mono.nvalid T φ).and
      fun s s' hs h e he => ⟨(h e he).1.mono T hs, (h e he).2.mono T hs⟩)
  exact Triple.appendM' hP' (Triple.pure _ fun s hs => hs.2.1)
    ((triple_items67 p r sb.2).pre fun s hs => ⟨hs.1, hs.2.2⟩)

end phases

/-- **Builder soundness for the packed construction.** -/
theorem triple_construction (p : Program) (r k : ℕ) :
    Triple (fun s => ∀ x ∈ inputs k, x.Valid T s) (construction p r k)
      fun φ s => φ.Valid T s := by
  have hP0 : Mono fun s => ∀ x ∈ inputs k, x.Valid T s :=
    Mono.forall_mem _ fun x => Mono.valid T x
  unfold construction
  refine Triple.bind hP0 (Triple.constant (T := T) _ 0) fun zero => ?_
  have h1 := hP0.and (Mono.valid T zero)
  refine Triple.bind h1 (Triple.constant (T := T) _ 1) fun one => ?_
  have h2 := h1.and (Mono.valid T one)
  refine Triple.bind h2 (Triple.fresh (T := T) _) fun q => ?_
  have h3 := h2.and (Mono.valid T q)
  refine Triple.bind h3 (Triple.fresh (T := T) _) fun c => ?_
  have h4 := h3.and (Mono.valid T c)
  refine Triple.bind h4 (Triple.fresh (T := T) _) fun K => ?_
  have h5 := h4.and (Mono.valid T K)
  refine Triple.bind h5 (Triple.fresh (T := T) _) fun B => ?_
  have h6 := h5.and (Mono.valid T B)
  refine Triple.bind h6 (Triple.fresh (T := T) _) fun T' => ?_
  have h7 := h6.and (Mono.valid T T')
  refine Triple.bind h7 (Triple.fresh (T := T) _) fun F => ?_
  have h8 := h7.and (Mono.valid T F)
  refine Triple.bind h8 (Triple.fresh (T := T) _) fun D => ?_
  have h9 := h8.and (Mono.valid T D)
  refine Triple.bind h9 (Triple.freshN (T := T) h9 r) fun R => ?_
  have h10 := h9.and (Mono.forall_mem R fun x => Mono.valid T x)
  refine Triple.bind h10 (Triple.freshN (T := T) h10 r) fun N => ?_
  have h11 := h10.and (Mono.forall_mem N fun x => Mono.valid T x)
  refine Triple.bind h11 (Triple.freshN (T := T) h11 _) fun S => ?_
  have h12 := h11.and (Mono.forall_mem S fun x => Mono.valid T x)
  refine Triple.bind h12 ((triple_packedFormulas (T := T) (a := inputs k) (zero := zero)
    (one := one) (q := q) (c := c) (K := K) (B := B) (T' := T') (F := F) (D := D) (R := R)
    (N := N) (S := S) p r).pre fun s hs => ?_) fun φs => ?_
  · obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hin, hz⟩, ho⟩, hq⟩, hc⟩, hK⟩, hB⟩, hT⟩, hF⟩, hD⟩, hR⟩, hN⟩, hS⟩ := hs
    exact ⟨⟨hz, ho, hq, hc, hK, hB, hT, hF, hD⟩, hin, hR, hN, hS⟩
  · exact Triple.pure _ fun s hs => by simp only [NForm.Valid]; exact hs.2

/-- **The polynomial of the compiled circuit** is the compilation of the formula of the packed
construction. -/
theorem compiled_poly (T : ExPoly) (p : Program) (r k : ℕ) :
    (compiled p r k).poly T = ((construction p r k).formula T k).compile :=
  toCircuit_poly (P := fun s => ∀ x ∈ inputs k, x.Valid T s) (fun x hx => by
    simp only [inputs, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact input_valid hi) (triple_construction p r k)

end ZInQ.Compiler.Packed
