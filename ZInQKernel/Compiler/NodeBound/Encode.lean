import ZInQKernel.Compiler.NodeBound.Items

/-!
# Node bounds of the node encoding

The node encoding of a formula `φ` creates at most `encA φ` addition and `encM φ` multiplication
nodes. In a list of formulas, an atom `a ≐ b` whose right side `b` is the right side of an
earlier atom of the list re-requests the product `(-1)·b`: the encoding of the list saves one
multiplication for each such repeat (`dupGo`).
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal

variable {P : List NatNode → Prop}

theorem Up.assume {α : Type} {p : Prop} {m : NM α} {a b : ℕ} {Q : α → List NatNode → Prop}
    (h : p → Up P m a b Q) : Up (fun l => P l ∧ p) m a b Q := ⟨fun s hs => (h hs.2).run s hs.1⟩

theorem seqM_square_up (hP : Mono P) (es : List Ex) :
    Up P (seqM (es.map square)) 0 es.length (fun sq _ => sq.length = es.length) := by
  induction es generalizing P with
  | nil => exact Up.pure fun _ _ => rfl
  | cons e es ih =>
    simp only [List.map_cons, seqM, square, mulL, mulFrom]
    simp only [NM.bind_assoc', NM.pure_bind']
    exact (Up.bind hP (Up.node_mul e.node e.node) fun i => Up.bind (Mono.and hP (Mono.idxOf? _ _))
      (ih (Mono.and hP (Mono.idxOf? _ _))) fun sq => Up.pure fun l hl => by
        simp [hl.2]).cost_of rfl (by simp; omega)

mutual

theorem encode_up (τ : Syntax.ExPoly) : ∀ (φ : NForm) {P : List NatNode → Prop}, Mono P →
    Up P (φ.encode τ) (encA φ) (encM φ) (fun _ _ => True)
  | .eq a b, P, hP => by
    apply Up.cost_of
    case h =>
      simp only [NForm.encode]
      up_norm
      up_run0
      all_goals trivial
    all_goals rfl
  | .atom f, P, hP => Up.pure fun _ _ => trivial
  | .call _ _ _ _ _, P, hP => Up.pure fun _ _ => trivial
  | .and fs, P, hP => by
    simp only [NForm.encode]
    refine (Up.bind hP (encodeList_up τ fs hP) fun es => Up.assume fun hes =>
      Up.bind hP ((seqM_square_up hP es).cost_of rfl hes) fun sq => Up.assume fun hsq =>
        (addL_up hP sq).cost_of (a' := fs.length - 1) (by rw [hsq, hes]) rfl).cost_of ?_ ?_
    · simp only [encA]; omega
    · simp only [encM]; omega
  | .or fs, P, hP => by
    simp only [NForm.encode]
    refine (Up.bind hP (encodeList_up τ fs hP) fun es => Up.assume fun hes =>
      ((mulL_up hP es).cost_of rfl (b' := fs.length - 1) (by rw [hes])).post
        (Q' := fun _ _ => True) fun _ _ _ => trivial).cost_of ?_ ?_
    · simp only [encA]; omega
    · simp only [encM]

theorem encodeList_up (τ : Syntax.ExPoly) : ∀ (fs : List NForm) {P : List NatNode → Prop},
    Mono P → Up P (NForm.encodeList τ fs) (encAL fs) (encML fs) (fun es _ => es.length = fs.length)
  | [], P, hP => Up.pure fun _ _ => rfl
  | f :: fs, P, hP => by
    simp only [NForm.encodeList]
    exact (Up.bind hP (encode_up τ f hP) fun e => Up.bind (Mono.and hP (Mono.const _))
      (encodeList_up τ fs (Mono.and hP (Mono.const _))) fun es => Up.pure fun l hl => by
        simp [hl.2]).cost_of (by simp [encAL]) (by simp [encML])

end

/-! ### Repeated right sides -/

/-- The right side of an atom `a ≐ b`. -/
def rhsNode : NForm → Option ℕ
  | .eq _ b => some b.node
  | _ => none

/-- The number of atoms of `φs` whose right side is in `seen` or is the right side of an earlier
atom of `φs`. -/
def dupGo : List NForm → List ℕ → ℕ
  | [], _ => 0
  | φ :: φs, seen =>
    match rhsNode φ with
    | some v => (if v ∈ seen then 1 else 0) + dupGo φs (v :: seen)
    | none => dupGo φs seen

theorem dupGo_le : ∀ (φs : List NForm) (seen : List ℕ), dupGo φs seen ≤ encML φs
  | [], _ => le_refl _
  | φ :: φs, seen => by
    cases φ with
    | eq a b =>
      have := dupGo_le φs (b.node :: seen)
      simp only [dupGo, rhsNode, encML, encM]; split_ifs <;> omega
    | atom f => have := dupGo_le φs seen; simp only [dupGo, rhsNode, encML]; omega
    | call _ _ _ _ _ => have := dupGo_le φs seen; simp only [dupGo, rhsNode, encML]; omega
    | and fs => have := dupGo_le φs seen; simp only [dupGo, rhsNode, encML]; omega
    | or fs => have := dupGo_le φs seen; simp only [dupGo, rhsNode, encML]; omega

/-- The product `(-1)·v` is present (the constant `-1` at its first index). -/
def NegMul (v : ℕ) (l : List NatNode) : Prop :=
  ∃ m1, l.idxOf? (.const (-1)) = some m1 ∧ NatNode.mul m1 v ∈ l

theorem Mono.negMul (v : ℕ) : Mono (NegMul v) := ⟨fun l l' h ⟨o, h1, h2⟩ =>
  ⟨o, (Mono.idxOf? _ _).mono l l' h h1, (Mono.mem _).mono l l' h h2⟩⟩

theorem encode_eq_up (τ : Syntax.ExPoly) (hP : Mono P) (a b : Ex) :
    Up P ((NForm.eq a b).encode τ) 1 1 (fun _ l => NegMul b.node l) := by
  simp only [NForm.encode]
  up_norm
  exact (Up.bind hP (Up.constant (-1)) fun c => Up.bind (Mono.and hP (Mono.idxOf? _ _))
    (Up.node_mul c.node b.node) fun i => Up.bind (Mono.and (Mono.and hP (Mono.idxOf? _ _))
      (Mono.idxOf? _ _)) (Up.node_add a.node i) fun j => Up.pure fun l hl =>
        ⟨c.node, hl.1.1.2, mem_of_idxOf? hl.1.2⟩).cost_of rfl rfl

theorem encode_eq_up_hit (τ : Syntax.ExPoly) (hP : Mono P) (a b : Ex)
    (hb : ∀ l, P l → NegMul b.node l) :
    Up P ((NForm.eq a b).encode τ) 1 0 (fun _ l => NegMul b.node l) := by
  simp only [NForm.encode]
  up_norm
  refine (Up.bind hP (Up.constant (-1)) fun c => Up.bind (Mono.and hP (Mono.idxOf? _ _))
    (Up.node_hit (n := .mul c.node b.node) fun l hl => ?_) fun i => Up.bind
      (Mono.and (Mono.and hP (Mono.idxOf? _ _)) (Mono.idxOf? _ _)) (Up.node_add a.node i)
        fun j => Up.pure fun l hl => ⟨c.node, hl.1.1.2, mem_of_idxOf? hl.1.2⟩).cost_of rfl rfl
  obtain ⟨m1, h1, h2⟩ := hb l hl.1
  rw [hl.2, Option.some.injEq] at h1
  exact h1 ▸ h2

/-- **The encoding of a list of formulas**, saving one multiplication per repeated right side. -/
theorem encodeList_up_dup (τ : Syntax.ExPoly) (fs : List NForm) :
    ∀ {P : List NatNode → Prop} (seen : List ℕ), Mono P → (∀ l, P l → ∀ v ∈ seen, NegMul v l) →
      Up P (NForm.encodeList τ fs) (encAL fs) (encML fs - dupGo fs seen)
        (fun es _ => es.length = fs.length) := by
  induction fs with
  | nil => exact fun _ _ _ => Up.pure fun _ _ => rfl
  | cons f fs ih =>
    intro P seen hP hseen
    simp only [NForm.encodeList]
    have hle := dupGo_le fs
    cases f
    case eq a b =>
      by_cases hv : b.node ∈ seen
      · refine (Up.bind hP (encode_eq_up_hit τ hP a b fun l hl => hseen l hl _ hv) fun e =>
          Up.bind (Mono.and hP (Mono.negMul _)) (ih (b.node :: seen) (Mono.and hP (Mono.negMul _))
            fun l hl v hv' => ?_) fun es => Up.pure fun l hl => by simp [hl.2]).cost_of
          (by simp [encAL, encA]) ?_
        · rcases List.mem_cons.1 hv' with rfl | hv'
          · exact hl.2
          · exact hseen l hl.1 v hv'
        · have := hle (b.node :: seen)
          simp only [encML, encM, dupGo, rhsNode, hv, ite_true]; omega
      · refine (Up.bind hP (encode_eq_up τ hP a b) fun e =>
          Up.bind (Mono.and hP (Mono.negMul _)) (ih (b.node :: seen) (Mono.and hP (Mono.negMul _))
            fun l hl v hv' => ?_) fun es => Up.pure fun l hl => by simp [hl.2]).cost_of
          (by simp [encAL, encA]) ?_
        · rcases List.mem_cons.1 hv' with rfl | hv'
          · exact hl.2
          · exact hseen l hl.1 v hv'
        · have := hle (b.node :: seen)
          simp only [encML, encM, dupGo, rhsNode, hv, ite_false]; omega
    all_goals (
      exact (Up.bind hP (encode_up τ _ hP) fun e => Up.bind (Mono.and hP (Mono.const _))
        (ih seen (Mono.and hP (Mono.const _)) fun l hl => hseen l hl.1) fun es =>
          Up.pure fun l hl => by simp [hl.2]).cost_of (by simp [encAL])
          (by have := hle seen; simp only [encML, dupGo, rhsNode]; omega))

/-- **The encoding of the conjunction of a list of formulas.** -/
theorem encode_and_up (τ : Syntax.ExPoly) (hP : Mono P) (fs : List NForm) :
    Up P ((NForm.and fs).encode τ) (encAL fs + (fs.length - 1))
      (encML fs - dupGo fs [] + fs.length) (fun _ _ => True) := by
  simp only [NForm.encode]
  exact (Up.bind hP (encodeList_up_dup τ fs [] hP fun _ _ _ h => absurd h List.not_mem_nil)
    fun es => Up.assume fun hes => Up.bind hP ((seqM_square_up hP es).cost_of rfl hes)
      fun sq => Up.assume fun hsq => ((addL_up hP sq).cost_of (a' := fs.length - 1)
        (by rw [hsq, hes]) rfl)).cost_of (by omega) (by omega)

end ZInQ.Compiler.NodeBound
