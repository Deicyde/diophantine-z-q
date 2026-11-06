import ZInQKernel.Compiler.Circuits.Packed.Construction
import ZInQKernel.Compiler.Circuits.Counts

/-!
# Variable and gadget counts of the packed construction

For a program `p` with `m` instructions, `s` of them sub instructions, `r` registers and `k`
inputs, the packed-history construction creates `m + r` mask macros, `r + s` bitAnd macros,
`3(r + s)` orthogonal macros, `m + 4r + 3s` binomial macros, `m + 4r + 3s` odd gadgets,
`2 + k + r + 2(m + 4r + 3s)` strict-inequality gadgets and `2 + 3(m + 4r + 3s)` power calls,
each with a private block of `79` variables. The compiled circuit has
`2k + 9 + 41r + 10m + 31s` explicit variables (the inputs included) and variable count
`(2k + 9 + 41r + 10m + 31s) + 79 (2 + 3m + 12r + 9s)`.

The counts hold for every program; validity is not needed.

(Blueprint: `compiler/natural/packed/packed-counts.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Packed

open Natural RM

theorem length_freshN (n : ℕ) (s : State) : ((freshN n) s).1.length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [freshN, ih]

theorem counts_freshN (n : ℕ) : Counts (freshN n) n 0 [] := by
  induction n with
  | zero => exact Counts.pure _
  | succ n ih =>
    exact (Counts.fresh.bind fun _ => ih.bind fun _ => Counts.pure _).congr (by ring) rfl rfl

theorem seqM_append {α : Type} (l₁ l₂ : List (NM α)) :
    seqM (l₁ ++ l₂) = (do let a ← seqM l₁; let b ← seqM l₂; pure (a ++ b)) := by
  funext s
  induction l₁ generalizing s with
  | nil => simp [seqM]
  | cons m ms ih => simp [seqM, ih]

theorem counts_seqM_append {α : Type} (l₁ l₂ : List (NM α)) {v₁ b₁ v₂ b₂ : ℕ}
    {L₁ L₂ : List MacroKind} (h₁ : Counts (seqM l₁) v₁ b₁ L₁) (h₂ : Counts (seqM l₂) v₂ b₂ L₂) :
    Counts (seqM (l₁ ++ l₂)) (v₁ + v₂) (b₁ + b₂) (L₁ ++ L₂) := by
  rw [seqM_append]
  exact (h₁.bind fun _ => h₂.bind fun _ => Counts.pure _).congr rfl rfl (by simp)

theorem counts_seqConcat_map {γ : Type} (l : List γ) (g : γ → NM (List NForm)) {v b : ℕ}
    {L : List MacroKind} (h : ∀ x, Counts (g x) v b L) :
    Counts (seqConcat (l.map g)) (l.length * v) (l.length * b) (List.replicate l.length L).flatten := by
  induction l with
  | nil => exact (Counts.pure _).congr (by simp) (by simp) (by simp)
  | cons x xs ih =>
    refine ((h x).bind fun _ => ih.bind fun _ => Counts.pure _).congr ?_ ?_ ?_
    · simp [Nat.succ_mul, add_comm]
    · simp [Nat.succ_mul, add_comm]
    · simp [List.replicate_succ]

theorem counts_registerMasks (K D T F Rj Nj : Ex) :
    Counts (registerMasks K D T F Rj Nj) 39 12 (maskLog ++ [.lt] ++ bitAndLog) := by
  counts_of registerMasks

theorem counts_registerEq (B Rj ιj : Ex) (decs incs : List Ex) :
    Counts (registerEq B Rj ιj decs incs) 0 0 [] := by
  counts_of registerEq

theorem counts_stateEq (B Si e : Ex) (ins : List Ex) : Counts (stateEq B Si e ins) 0 0 [] := by
  counts_of stateEq

theorem counts_subBranches (zero : Ex) (S N : List Ex) (i : ℕ) (p : Program) :
    Counts (subBranches zero S N i p) (31 * p.subCount) (9 * p.subCount)
      (List.replicate p.subCount bitAndLog).flatten := by
  induction p generalizing i with
  | nil => exact Counts.pure _
  | cons ins rest ih =>
    cases ins with
    | dec j x y =>
      have hfs : ∀ V W : Ex, Counts (seqM [bitAnd .hierarchical V (S.getD i zero) (N.getD j zero),
          do pure (.eq (S.getD i zero) (← addL [V, W]))]) 29 9 bitAndLog := fun V W =>
        (Counts.seqM_cons (Counts.bitAnd V _ _) (Counts.seqM_cons ((Counts.addL [V, W]).bind
          fun e => Counts.pure (NForm.eq (S.getD i zero) e)) Counts.seqM_nil)).congr rfl rfl
          (by simp)
      have h := Counts.fresh.bind fun V => Counts.fresh.bind fun W =>
        (hfs V W).bind fun fs => (ih (i + 1)).bind fun rest' =>
            Counts.pure (fs ++ rest'.1, (i, V, W) :: rest'.2)
      refine h.congr ?_ ?_ ?_
      · simp [Program.subCount, List.countP_cons, Instr.isDec]; ring
      · simp [Program.subCount, List.countP_cons, Instr.isDec]; ring
      · simp [Program.subCount, List.countP_cons, Instr.isDec, List.replicate_succ]
    | inc j x =>
      simpa [subBranches, Program.subCount, List.countP_cons, Instr.isDec] using ih (i + 1)
    | halt =>
      simpa [subBranches, Program.subCount, List.countP_cons, Instr.isDec] using ih (i + 1)


theorem Counts.bind'_eq {α β : Type} {m : NM α} {f : α → NM β} {v₁ b₁ v₂ b₂ v b : ℕ}
    {L₁ L₂ L : List MacroKind} {P : α → Prop} (hf : ∀ a, P a → Counts (f a) v₂ b₂ L₂)
    (hm : Counts m v₁ b₁ L₁) (hP : ∀ s, P (m s).1) (hv : v₁ + v₂ = v) (hb : b₁ + b₂ = b)
    (hL : L₁ ++ L₂ = L) : Counts (m >>= f) v b L := by
  subst hv hb hL; exact Counts.bind' hm hP hf

theorem Counts.seqM_map_len {α γ : Type} (l : List γ) (g : γ → NM α) {n v b : ℕ}
    {L : List MacroKind} (hl : l.length = n) (h : ∀ x, Counts (g x) v b L) :
    Counts (seqM (l.map g)) (n * v) (n * b) (List.replicate n L).flatten := by
  subst hl; exact Counts.seqM_map l g h

/-- The macro log of the packed-history construction. -/
def packedLog (p : Program) (r k : ℕ) : List MacroKind :=
  [.lt, .power, .lt, .power] ++ (List.replicate k [.lt]).flatten ++
    (List.replicate p.length maskLog).flatten ++
    (List.replicate r (maskLog ++ [.lt] ++ bitAndLog)).flatten ++
    (List.replicate p.subCount bitAndLog).flatten

theorem counts_appendM {m₁ m₂ : NM (List NForm)} {v₁ b₁ v₂ b₂ : ℕ} {L₁ L₂ : List MacroKind}
    (h₁ : Counts m₁ v₁ b₁ L₁) (h₂ : Counts m₂ v₂ b₂ L₂) :
    Counts (appendM m₁ m₂) (v₁ + v₂) (b₁ + b₂) (L₁ ++ L₂) :=
  (h₁.bind fun _ => h₂.bind fun _ => Counts.pure _).congr rfl rfl (by simp)

theorem counts_items1 (p : Program) (a : List Ex) (zero q c K B T : Ex) :
    Counts (items1 p a zero q c K B T) (2 + a.length) 2
      ([.lt, .power, .lt, .power] ++ (List.replicate a.length [.lt]).flatten) := by
  unfold items1
  have h1 : Counts (seqM [lt zero c, do power .hierarchical K (← constant 2) c,
      do pure (.eq B (← scale 4 K)), do lt (← constant p.length) B, power .hierarchical T B q])
      2 2 [.lt, .power, .lt, .power] := by
    counts_tac
    all_goals first | rfl | simp
  exact (counts_seqM_append _ _ h1 (Counts.seqM_map a (fun ai => lt ai K) fun ai =>
    Counts.lt ai K)).congr (by ring) rfl rfl

theorem counts_items2 (zero one K B T F D : Ex) (S : List Ex) :
    Counts (items2 zero one K B T F D S) 0 0 [] := by
  counts_of items2

theorem counts_items3 (F : Ex) (S : List Ex) :
    Counts (items3 F S) (S.length * 9) (S.length * 3) (List.replicate S.length maskLog).flatten :=
  Counts.seqM_map S _ fun x => Counts.mask x F

theorem counts_items4 (r : ℕ) (zero K D T F : Ex) (R N : List Ex) :
    Counts (items4 r zero K D T F R N) (r * 39) (r * 12)
      (List.replicate r (maskLog ++ [.lt] ++ bitAndLog)).flatten := by
  have := counts_seqConcat_map (List.range r) _ fun j =>
    counts_registerMasks K D T F (R.getD j zero) (N.getD j zero)
  rw [List.length_range] at this
  exact this

theorem counts_items6 (p : Program) (r : ℕ) (a : List Ex) (zero B : Ex) (R S : List Ex)
    (vw : List (ℕ × Ex × Ex)) : Counts (items6 p r a zero B R S vw) 0 0 [] :=
  (Counts.seqM_map _ _ fun j => counts_registerEq _ _ _ _ _).congr (by simp) (by simp) (by simp)

theorem counts_items7 (p : Program) (zero one B : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex)) :
    Counts (items7 p zero one B S vw) 0 0 [] :=
  (Counts.seqM_map _ _ fun i => counts_stateEq _ _ _ _).congr (by simp) (by simp) (by simp)

theorem counts_packedFormulas (p : Program) (r : ℕ) (a : List Ex) (zero one q c K B T F D : Ex)
    (R N S : List Ex) (hS : S.length = p.length) :
    Counts (packedFormulas p r a zero one q c K B T F D R N S)
      (2 + a.length + 9 * p.length + 39 * r + 31 * p.subCount)
      (2 + 3 * p.length + 12 * r + 9 * p.subCount)
      ([.lt, .power, .lt, .power] ++ (List.replicate a.length [.lt]).flatten ++
        (List.replicate p.length maskLog).flatten ++
        (List.replicate r (maskLog ++ [.lt] ++ bitAndLog)).flatten ++
        (List.replicate p.subCount bitAndLog).flatten) := by
  unfold packedFormulas
  have hsb : ∀ sb : List NForm × List (ℕ × Ex × Ex), Counts (appendM (pure sb.1) (appendM
      (items6 p r a zero B R S sb.2) (items7 p zero one B S sb.2))) 0 0 [] := fun sb =>
    (counts_appendM (Counts.pure sb.1) (counts_appendM (counts_items6 _ _ _ _ _ _ _ _)
      (counts_items7 _ _ _ _ _ _))).congr rfl rfl rfl
  have h5 := (counts_subBranches zero S N 0 p).bind hsb
  have := counts_appendM (counts_items1 p a zero q c K B T) (counts_appendM
    (counts_items2 zero one K B T F D S) (counts_appendM (counts_items3 F S)
      (counts_appendM (counts_items4 r zero K D T F R N) h5)))
  rw [hS] at this
  refine this.congr (by ring) (by ring) (by simp)

theorem counts_construction (p : Program) (r k : ℕ) :
    Counts (construction p r k) (9 + k + 41 * r + 10 * p.length + 31 * p.subCount)
      (2 + 3 * p.length + 12 * r + 9 * p.subCount) (packedLog p r k) := by
  unfold construction
  apply Counts.bind_eq (hm := Counts.constant 0); intro zero
  apply Counts.bind_eq (hm := Counts.constant 1); intro one
  apply Counts.bind_eq (hm := Counts.fresh); intro q
  apply Counts.bind_eq (hm := Counts.fresh); intro c
  apply Counts.bind_eq (hm := Counts.fresh); intro K
  apply Counts.bind_eq (hm := Counts.fresh); intro B
  apply Counts.bind_eq (hm := Counts.fresh); intro T
  apply Counts.bind_eq (hm := Counts.fresh); intro F
  apply Counts.bind_eq (hm := Counts.fresh); intro D
  apply Counts.bind_eq (hm := counts_freshN r); intro R
  apply Counts.bind_eq (hm := counts_freshN r); intro N
  apply Counts.bind'_eq (P := fun S => S.length = p.length) (hm := counts_freshN p.length)
    (hP := fun s => length_freshN _ s)
  intro S hS
  apply Counts.bind_eq (hm := counts_packedFormulas p r (inputs k) zero one q c K B T F D R N S hS)
  intro φs
  · exact Counts.pure _
  all_goals try (with_reducible rfl)
  · simp only [inputs, List.length_map, List.length_range]; ring
  · ring
  · simp [packedLog, inputs]

theorem blocks_length (C : NatCircuit) : C.blocks.length = C.nodes.countP NatNode.isCall := by
  unfold NatCircuit.blocks
  rw [List.length_filterMap_eq_countP]
  congr 1
  funext n
  cases n <;> rfl

/-- **Variable and gadget counts of the packed construction.** With `m` instructions, `s` sub
instructions, `r` registers and `k` inputs: the macro log records `m + r` masks, `r + s`
bitAnds, `3(r + s)` orthogonals, `m + 4r + 3s` binomials, `m + 4r + 3s` odd gadgets,
`2 + k + r + 2(m + 4r + 3s)` strict inequalities and `2 + 3(m + 4r + 3s)` power macros; the
compiled circuit has that many call nodes (blocks), `2k + 9 + 41r + 10m + 31s` explicit
variables and variable count `(2k + 9 + 41r + 10m + 31s) + 79 (2 + 3m + 12r + 9s)`. -/
theorem packed_counts (p : Program) (r k : ℕ) :
    let m := p.length
    let s := p.subCount
    let L := (construction p r k (State.init k)).2.log
    L.count .mask = m + r ∧ L.count .bitAnd = r + s ∧ L.count .orthogonal = 3 * (r + s) ∧
    L.count .binomial = m + 4 * r + 3 * s ∧ L.count .odd = m + 4 * r + 3 * s ∧
    L.count .lt = 2 + k + r + 2 * (m + 4 * r + 3 * s) ∧
    L.count .power = 2 + 3 * (m + 4 * r + 3 * s) ∧
    (compiled p r k).blocks.length = 2 + 3 * m + 12 * r + 9 * s ∧
    (compiled p r k).explicitVars.length = 2 * k + 9 + 41 * r + 10 * m + 31 * s ∧
    (compiled p r k).varCount =
      (2 * k + 9 + 41 * r + 10 * m + 31 * s) + 79 * (2 + 3 * m + 12 * r + 9 * s) := by
  intro m s L
  obtain ⟨h1, h2, h3, h4, h5⟩ := counts_construction p r k (State.init k)
  obtain ⟨e1, e2, e3, e4, e5⟩ := counts_encode Syntax.ExPoly.empty
    (construction p r k (State.init k)).1 (construction p r k (State.init k)).2
  have hL : L = packedLog p r k := by simpa [L, State.init] using h5
  have hinit : callCount (State.init k) = 0 := by
    simp [callCount, State.init, List.countP_eq_zero, NatNode.isCall]
  have hb : (compiled p r k).blocks.length = 2 + 3 * m + 12 * r + 9 * s := by
    rw [blocks_length, compiled, NM.toCircuit_nodes]
    change callCount _ = _
    rw [e4, h4, hinit]
    simp only [m, s]; ring
  have hv : (compiled p r k).explicitVars.length = 2 * k + 9 + 41 * r + 10 * m + 31 * s := by
    rw [compiled, NM.toCircuit_explicitVars, e2, h2]
    simp only [State.init, List.length_map, List.length_range, m, s]
    ring
  have hn : (compiled p r k).varCount =
      (2 * k + 9 + 41 * r + 10 * m + 31 * s) + 79 * (2 + 3 * m + 12 * r + 9 * s) := by
    rw [compiled, NM.toCircuit_varCount, e1, h1]
    simp only [State.init, powerWitnesses, m, s]
    ring
  have hc : ∀ k' : MacroKind, L.count k' = (packedLog p r k).count k' := fun k' => by rw [hL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hb, hv, hn⟩
  all_goals simp only [hc, packedLog, List.count_append, List.count_flatten, List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  all_goals simp [maskLog, bitAndLog, orthogonalLog, binomialLog]
  all_goals ring

end ZInQ.Compiler.Packed
