import ZInQKernel.Syntax.Language

/-!
# Scope of template constructions

The templates of the library are `Build` programs (`ZInQKernel.Syntax.Language.Build`). This
file gives the tools that prove, for one program at a time, that the constructed template is
well formed and that its call blocks are private, without expanding any polynomial.

* `Avail N B i`: the index `i` lies below the final counter `N` and outside every block of the
  list `B` (in practice the concrete list of call blocks of the template).
* `PairIn`, `CodeIn` and `FOk` extend the variable predicate `VarsIn` to pairs, point codes and
  formulas; `FOk G N φ` also says that the callees of `φ` are well formed and that its blocks
  end below `N`.
* `Build.WP b s K` is the weakest-precondition reading `K (b s).1 (b s).2` of a program run from
  the state `s`. The rules `wp_bind`, `wp_fresh`, `wp_call`, … keep the values abstract and only
  check numeric side conditions on the counter, by `decide`.
* `Build.template_wf_of_fok` and `Build.template_rel_iff_lift` turn a final `FOk` statement
  into well-formedness and into the relation of the template with every call atom replaced by
  the callee relation (`Formula.Lift`).
-/

namespace ZInQ.Syntax

open MvPolynomial

/-! ### Available indices -/

/-- `i` lies outside every block of `B` (Boolean form). -/
def blockFree (B : List (ℕ × ℕ)) (i : ℕ) : Bool :=
  B.all fun b => !(decide (b.1 ≤ i) && decide (i < b.1 + b.2))

theorem blockFree_iff (B : List (ℕ × ℕ)) (i : ℕ) : blockFree B i = true ↔ ¬ InBlocks B i := by
  simp only [blockFree, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, InBlocks, InBlock, not_exists, not_and]
  refine forall_congr' fun b => imp_congr_right fun _ => ?_
  omega

/-- The indices that values of a construction may use: below `N` and outside the blocks
`B`. -/
def Avail (N : ℕ) (B : List (ℕ × ℕ)) (i : ℕ) : Prop := i < N ∧ blockFree B i = true

instance (N : ℕ) (B : List (ℕ × ℕ)) (i : ℕ) : Decidable (Avail N B i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Variable predicates for pairs and codes -/

/-- Both components of a pair satisfy `VarsIn`. -/
def PairIn (u : Pair) (G : ℕ → Prop) : Prop := VarsIn u.1 G ∧ VarsIn u.2 G

/-- Every parameter polynomial satisfies `VarsIn`. -/
def ArgsIn {n : ℕ} (g : Fin n → Poly) (G : ℕ → Prop) : Prop := ∀ k, VarsIn (g k) G

/-- All five coordinates of a code satisfy `VarsIn`. -/
def CodeIn (p : Code) (G : ℕ → Prop) : Prop := ∀ i, VarsIn (p i) G

namespace VarsIn

variable {G : ℕ → Prop}

theorem bind₁ {σ : Type*} {f : σ → Poly} {P : MvPolynomial σ ℤ} (h : ∀ i, VarsIn (f i) G) :
    VarsIn (MvPolynomial.bind₁ f P) G := by
  classical
  intro i hi
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (vars_bind₁ f P hi)
  exact h j i hj

theorem bind₁_fin {n : ℕ} {f : Fin n → Poly} {P : MvPolynomial (Fin n) ℤ}
    (h : ∀ i, VarsIn (f i) G) : VarsIn (MvPolynomial.bind₁ f P) G := bind₁ h

theorem neg_one_mul {f : Poly} (h : VarsIn f G) : VarsIn ((-1 : Poly) * f) G :=
  (VarsIn.neg (VarsIn.one G)).mul h

end VarsIn

namespace PairIn

variable {G : ℕ → Prop} {u v : Pair}

theorem mk {a b : Poly} (ha : VarsIn a G) (hb : VarsIn b G) : PairIn (a, b) G := ⟨ha, hb⟩

theorem add (hu : PairIn u G) (hv : PairIn v G) : PairIn (u.add v) G :=
  ⟨hu.1.add hv.1, hu.2.add hv.2⟩

theorem neg (hu : PairIn u G) : PairIn u.neg G := ⟨hu.1.neg, hu.2.neg⟩

theorem sub (hu : PairIn u G) (hv : PairIn v G) : PairIn (u.sub v) G := hu.add hv.neg

theorem smul {k : Poly} (hk : VarsIn k G) (hu : PairIn u G) : PairIn (Pair.smul k u) G :=
  ⟨hk.mul hu.1, hk.mul hu.2⟩

theorem mul (hu : PairIn u G) (hv : PairIn v G) : PairIn (u.mul v) G :=
  ⟨(hu.1.mul hv.1).add ((VarsIn.ofNat 2 G).mul (hu.2.mul hv.2)),
    (hu.1.mul hv.2).add (hu.2.mul hv.1)⟩

theorem sq (hu : PairIn u G) : PairIn u.sq G := hu.mul hu

theorem ofInt (a b : ℤ) : PairIn (Pair.ofInt a b) G := ⟨VarsIn.C a G, VarsIn.C b G⟩

theorem one : PairIn Pair.one G := ofInt 1 0

theorem zero : PairIn Pair.zero G := ofInt 0 0

theorem A : PairIn Pair.A G := ofInt _ _

theorem delta : PairIn Pair.delta G := ofInt _ _

theorem conj (hu : PairIn u G) : PairIn u.conj G := ⟨hu.1, hu.2.neg⟩

theorem norm (hu : PairIn u G) : VarsIn u.norm G := VarsIn.norm hu.1 hu.2

theorem powAux (n : ℕ) {r q : Pair} (hr : PairIn r G) (hq : PairIn q G) :
    PairIn (Pair.powAux n r q) G := by
  induction n using Nat.strong_induction_on generalizing r q with
  | _ n ih =>
    rw [Pair.powAux]
    split_ifs with h0 h1 h2 h2
    · exact hr
    · exact hr.mul hq
    · exact ih _ (by omega) (hr.mul hq) hq.sq
    · exact hr
    · exact ih _ (by omega) hr hq.sq

theorem pow (hu : PairIn u G) (n : ℕ) : PairIn (u.pow n) G := powAux n one hu

theorem list_foldl {α : Type*} {f : Pair → α → Pair} {P : α → Prop} {l : List α} {u : Pair}
    (hu : PairIn u G) (hf : ∀ v a, PairIn v G → P a → PairIn (f v a) G) (hl : ∀ a ∈ l, P a) :
    PairIn (l.foldl f u) G := by
  induction l generalizing u with
  | nil => exact hu
  | cons a l ih =>
    rw [List.foldl_cons]
    exact ih (hf u a hu (hl a List.mem_cons_self)) fun b hb => hl b (List.mem_cons_of_mem _ hb)

end PairIn

namespace CodeIn

variable {G : ℕ → Prop} {p : Code}

theorem x (hp : CodeIn p G) : PairIn p.x G := ⟨hp 1, hp 2⟩

theorem y (hp : CodeIn p G) : PairIn p.y G := ⟨hp 3, hp 4⟩

theorem mk {a b c d e : Poly} (ha : VarsIn a G) (hb : VarsIn b G) (hc : VarsIn c G)
    (hd : VarsIn d G) (he : VarsIn e G) : CodeIn ![a, b, c, d, e] G := by
  intro i
  fin_cases i <;> assumption

theorem O : CodeIn Code.O G :=
  mk (VarsIn.one G) (VarsIn.zero G) (VarsIn.zero G) (VarsIn.zero G) (VarsIn.zero G)

theorem neg (hp : CodeIn p G) : CodeIn p.neg G :=
  mk (hp 0) (hp 1) (hp 2) (hp 3).neg (hp 4).neg

end CodeIn

/-! ### Formulas -/

/-- The scope facts of a formula built by a construction: callees well formed, parameter
polynomials and atoms using only `G`, call blocks ending below `N`. -/
def FOk (G : ℕ → Prop) (N : ℕ) (φ : Formula) : Prop :=
  (∀ τ ∈ φ.callees, τ.WF) ∧ (∀ f ∈ φ.freePolys, VarsIn f G) ∧ (∀ b ∈ φ.blocks, b.1 + b.2 ≤ N)

namespace FOk

variable {G : ℕ → Prop} {N : ℕ}

theorem eq {a b : Poly} (ha : VarsIn a G) (hb : VarsIn b G) : FOk G N (.eq a b) := by
  refine ⟨by simp [Formula.callees], ?_, by simp [Formula.blocks]⟩
  simp only [Formula.freePolys, List.mem_cons, List.not_mem_nil, or_false]
  rintro f (rfl | rfl) <;> assumption

theorem atom {f : Poly} (hf : VarsIn f G) : FOk G N (.atom f) := by
  refine ⟨by simp [Formula.callees], ?_, by simp [Formula.blocks]⟩
  simp only [Formula.freePolys, List.mem_cons, List.not_mem_nil, or_false]
  rintro g rfl; exact hf

theorem call {τ : ExPoly} {g : Fin τ.params → Poly} {w : ℕ} (hτ : τ.WF)
    (hg : ∀ k, VarsIn (g k) G) (hw : w + τ.witnesses ≤ N) : FOk G N (.call τ g w) := by
  refine ⟨by simpa [Formula.callees] using hτ, ?_, by simpa [Formula.blocks] using hw⟩
  simp only [Formula.freePolys, List.mem_ofFn]
  rintro f ⟨k, rfl⟩; exact hg k

theorem and_iff {fs : List Formula} : FOk G N (.and fs) ↔ ∀ φ ∈ fs, FOk G N φ := by
  simp only [FOk, Formula.callees_and, Formula.freePolys_and, Formula.blocks_and,
    List.mem_flatMap, forall_exists_index, and_imp]
  constructor
  · rintro ⟨h1, h2, h3⟩ φ hφ
    exact ⟨fun τ hτ => h1 τ φ hφ hτ, fun f hf => h2 f φ hφ hf, fun b hb => h3 b φ hφ hb⟩
  · intro h
    exact ⟨fun τ φ hφ hτ => (h φ hφ).1 τ hτ, fun f φ hφ hf => (h φ hφ).2.1 f hf,
      fun b φ hφ hb => (h φ hφ).2.2 b hb⟩

theorem or_iff {fs : List Formula} : FOk G N (.or fs) ↔ ∀ φ ∈ fs, FOk G N φ := by
  simp only [FOk, Formula.callees_or, Formula.freePolys_or, Formula.blocks_or,
    List.mem_flatMap, forall_exists_index, and_imp]
  constructor
  · rintro ⟨h1, h2, h3⟩ φ hφ
    exact ⟨fun τ hτ => h1 τ φ hφ hτ, fun f hf => h2 f φ hφ hf, fun b hb => h3 b φ hφ hb⟩
  · intro h
    exact ⟨fun τ φ hφ hτ => (h φ hφ).1 τ hτ, fun f φ hφ hf => (h φ hφ).2.1 f hf,
      fun b φ hφ hb => (h φ hφ).2.2 b hb⟩

theorem and_nil : FOk G N (.and []) := and_iff.2 fun _ h => absurd h List.not_mem_nil

theorem and_cons {φ : Formula} {fs : List Formula} (hφ : FOk G N φ) (hfs : FOk G N (.and fs)) :
    FOk G N (.and (φ :: fs)) :=
  and_iff.2 fun ψ hψ => (List.mem_cons.1 hψ).elim (fun h => h ▸ hφ) fun h => and_iff.1 hfs ψ h

theorem or_nil : FOk G N (.or []) := or_iff.2 fun _ h => absurd h List.not_mem_nil

theorem or_cons {φ : Formula} {fs : List Formula} (hφ : FOk G N φ) (hfs : FOk G N (.or fs)) :
    FOk G N (.or (φ :: fs)) :=
  or_iff.2 fun ψ hψ => (List.mem_cons.1 hψ).elim (fun h => h ▸ hφ) fun h => or_iff.1 hfs ψ h

theorem and_of_forall {fs : List Formula} (h : ∀ φ ∈ fs, FOk G N φ) : FOk G N (.and fs) :=
  and_iff.2 h

theorem and_append {fs gs : List Formula} (hf : FOk G N (.and fs)) (hg : FOk G N (.and gs)) :
    FOk G N (.and (fs ++ gs)) :=
  and_iff.2 fun φ hφ => (List.mem_append.1 hφ).elim (and_iff.1 hf φ) (and_iff.1 hg φ)

theorem mono {φ : Formula} {N' : ℕ} (h : FOk G N φ) (hN : N ≤ N') : FOk G N' φ :=
  ⟨h.1, h.2.1, fun b hb => (h.2.2 b hb).trans hN⟩

theorem feq {u v : Pair} (hu : PairIn u G) (hv : PairIn v G) : FOk G N (feq u v) :=
  and_cons (eq hu.1 hv.1) (and_cons (eq hu.2 hv.2) and_nil)

theorem peq {p q : Code} (hp : CodeIn p G) (hq : CodeIn q G) : FOk G N (peq p q) :=
  and_iff.2 fun φ hφ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
    exact eq (hp i) (hq i)

theorem isO {p : Code} (hp : CodeIn p G) : FOk G N (isO p) := peq hp CodeIn.O

theorem fin {p : Code} (hp : CodeIn p G) : FOk G N (fin p) := eq (hp 0) (VarsIn.zero G)

theorem curve {X Y : Pair} (hX : PairIn X G) (hY : PairIn Y G) : FOk G N (curve X Y) :=
  feq hY.sq ((hX.sq.mul hX).add (PairIn.A.mul hX))

theorem nzFormula {a : Poly} {c : ℕ} (ha : VarsIn a G) (hc : G c) :
    FOk G N (nzFormula a c) := eq (ha.mul (VarsIn.X hc)) (VarsIn.one G)

theorem posFormula {a : Poly} {c : ℕ} (ha : VarsIn a G) (h0 : G c) (h1 : G (c + 1))
    (h2 : G (c + 2)) (h3 : G (c + 3)) : FOk G N (posFormula a c) :=
  eq (ha.mul (((((VarsIn.X h0).pow 2).add ((VarsIn.X h1).pow 2)).add ((VarsIn.X h2).pow 2)).add
    ((VarsIn.X h3).pow 2))) (VarsIn.one G)

theorem divFormula {n d q : Pair} {k : ℕ} (hn : PairIn n G) (hd : PairIn d G) (hq : PairIn q G)
    (hk : G k) : FOk G N (divFormula n d q k) :=
  and_cons (nzFormula hd.norm hk) (and_cons (feq (hd.mul hq) hn) and_nil)

theorem zFormula {p : Code} {ζ : Pair} {k : ℕ} (hp : CodeIn p G) (hζ : PairIn ζ G) (hk : G k) :
    FOk G N (zFormula p ζ k) :=
  or_cons (and_cons (isO hp) (and_cons (feq hζ PairIn.zero) and_nil))
    (or_cons (and_cons (fin hp) (and_cons (nzFormula hp.y.norm hk)
      (and_cons (feq (hp.y.mul hζ) hp.x.neg) and_nil))) or_nil)

theorem ixFormula {p : Code} {v : Pair} (hp : CodeIn p G) (hv : PairIn v G) :
    FOk G N (ixFormula p v) :=
  or_cons (and_cons (isO hp) (and_cons (feq hv PairIn.zero) and_nil))
    (or_cons (and_cons (fin hp) (and_cons (feq (hp.x.mul hv) PairIn.one) and_nil)) or_nil)

end FOk

/-- A formula with the scope facts compiles to a polynomial whose variables lie below `N`,
when `G` only allows indices below `N`. -/
theorem varsLT_compile_of_fok {G : ℕ → Prop} {N : ℕ} {φ : Formula} (h : FOk G N φ)
    (hG : ∀ i, G i → i < N) : VarsLT φ.compile N := by
  intro i hi
  rcases Formula.mem_vars_compile h.1 hi with ⟨f, hf, hif⟩ | ⟨b, hb, hib⟩
  · exact hG i (h.2.1 f hf i hif)
  · have := h.2.2 b hb
    exact lt_of_lt_of_le hib.2 this

/-! ### Blocks of the gadget formulas -/

namespace Formula

theorem blocks_eq_nil_of_forall {fs : List Formula} (h : ∀ φ ∈ fs, φ.blocks = []) :
    (Formula.and fs).blocks = [] := by
  rw [blocks_and, List.flatMap_eq_nil_iff]; exact h

end Formula

@[simp] theorem blocks_feq (u v : Pair) : (feq u v).blocks = [] := by
  simp [feq, Formula.blocks]

@[simp] theorem blocks_peq (p q : Code) : (peq p q).blocks = [] := by
  refine Formula.blocks_eq_nil_of_forall fun φ hφ => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
  simp [Formula.blocks]

@[simp] theorem blocks_isO (p : Code) : (isO p).blocks = [] := blocks_peq _ _

@[simp] theorem blocks_fin (p : Code) : (fin p).blocks = [] := by simp [fin, Formula.blocks]

@[simp] theorem blocks_curve (X Y : Pair) : (curve X Y).blocks = [] := blocks_feq _ _

@[simp] theorem blocks_nzFormula (a : Poly) (c : ℕ) : (nzFormula a c).blocks = [] := by
  simp [nzFormula, Formula.blocks]

@[simp] theorem blocks_posFormula (a : Poly) (c : ℕ) : (posFormula a c).blocks = [] := by
  simp [posFormula, Formula.blocks]

@[simp] theorem blocks_zFormula (p : Code) (ζ : Pair) (k : ℕ) : (zFormula p ζ k).blocks = [] := by
  simp [zFormula]

@[simp] theorem blocks_ixFormula (p : Code) (v : Pair) : (ixFormula p v).blocks = [] := by
  simp [ixFormula]

@[simp] theorem blocks_divFormula (n d q : Pair) (k : ℕ) : (divFormula n d q k).blocks = [] := by
  simp [divFormula]

/-! ### Weakest preconditions of constructions -/

namespace Build

/-- `K` holds of the value and the final state of `b` run from `s`. -/
def WP {α : Type} (b : Build α) (s : BuildState) (K : α → BuildState → Prop) : Prop :=
  K (b s).1 (b s).2

variable {α β : Type} {s : BuildState}

theorem wp_bind {b : Build α} {f : α → Build β} {K : β → BuildState → Prop}
    (h : WP b s fun a s' => WP (f a) s' K) : WP (b >>= f) s K := h

theorem wp_pure {a : α} {K : α → BuildState → Prop} (h : K a s) : WP (pure a) s K := h

theorem wp_fresh {G : ℕ → Prop} {K : Poly → BuildState → Prop} (hs : G s.next)
    (h : ∀ v, VarsIn v G → K v { s with next := s.next + 1 }) : WP fresh s K :=
  h _ (VarsIn.X hs)

theorem wp_freshPoint {G : ℕ → Prop} {K : Code → BuildState → Prop} (h0 : G s.next)
    (h1 : G (s.next + 1)) (h2 : G (s.next + 2)) (h3 : G (s.next + 3)) (h4 : G (s.next + 4))
    (h : ∀ p, CodeIn p G → K p { s with next := s.next + 5 }) : WP freshPoint s K := by
  unfold WP
  rw [freshPoint_apply]
  refine h _ fun i => VarsIn.X ?_
  fin_cases i
  · exact h0
  all_goals assumption

theorem wp_call {G : ℕ → Prop} {N m : ℕ} {τ : ExPoly} {g : Fin τ.params → Poly}
    {K : Formula → BuildState → Prop} (hτ : τ.WF) (hm : τ.witnesses = m)
    (hg : ArgsIn g G) (hN : s.next + m ≤ N)
    (h : ∀ φ, FOk G N φ → φ.blocks = [(s.next, m)] → K φ { s with next := s.next + m }) :
    WP (call τ g) s K := by
  unfold WP
  rw [call_apply]
  subst hm
  exact h _ (FOk.call hτ hg hN) (by simp [Formula.blocks])

theorem wp_nz {G : ℕ → Prop} {N : ℕ} {a : Poly} {K : Formula → BuildState → Prop}
    (hs : G s.next) (ha : VarsIn a G)
    (h : ∀ φ, FOk G N φ → φ.blocks = [] → K φ { s with next := s.next + 1 }) :
    WP (nz a) s K := by
  unfold WP
  rw [nz_apply]
  exact h _ (FOk.nzFormula ha hs) (by simp [nzFormula, Formula.blocks])

theorem wp_fnz {G : ℕ → Prop} {N : ℕ} {u : Pair} {K : Formula → BuildState → Prop}
    (hs : G s.next) (hu : PairIn u G)
    (h : ∀ φ, FOk G N φ → φ.blocks = [] → K φ { s with next := s.next + 1 }) :
    WP (fnz u) s K :=
  wp_nz hs hu.norm h

theorem wp_pos {G : ℕ → Prop} {N : ℕ} {a : Poly} {K : Formula → BuildState → Prop}
    (h0 : G s.next) (h1 : G (s.next + 1)) (h2 : G (s.next + 2)) (h3 : G (s.next + 3))
    (ha : VarsIn a G) (h : ∀ φ, FOk G N φ → φ.blocks = [] → K φ { s with next := s.next + 4 }) :
    WP (pos a) s K := by
  unfold WP
  rw [pos_apply]
  exact h _ (FOk.posFormula ha h0 h1 h2 h3) (by simp [posFormula, Formula.blocks])

theorem wp_fdiv {G : ℕ → Prop} {N : ℕ} {n d : Pair} {K : Pair × Formula → BuildState → Prop}
    (h0 : G s.next) (h1 : G (s.next + 1)) (h2 : G (s.next + 2)) (hn : PairIn n G)
    (hd : PairIn d G)
    (h : ∀ q φ, PairIn q G → FOk G N φ → φ.blocks = [] → K (q, φ) { s with next := s.next + 3 }) :
    WP (fdiv n d) s K := by
  unfold WP
  rw [fdiv_apply]
  exact h _ _ ⟨VarsIn.X h0, VarsIn.X h1⟩ (FOk.divFormula hn hd ⟨VarsIn.X h0, VarsIn.X h1⟩ h2)
    (by simp [divFormula, nzFormula, feq, Formula.blocks])

theorem wp_zGadget {G : ℕ → Prop} {N : ℕ} {p : Code} {ζ : Pair}
    {K : Formula → BuildState → Prop} (hs : G s.next) (hp : CodeIn p G) (hζ : PairIn ζ G)
    (h : ∀ φ, FOk G N φ → φ.blocks = [] → K φ { s with next := s.next + 1 }) :
    WP (zGadget p ζ) s K := by
  unfold WP
  rw [zGadget_apply]
  exact h _ (FOk.zFormula hp hζ hs)
    (by simp [zFormula, isO, peq, fin, nzFormula, feq, Formula.blocks])

/-- The value of a rational-constant request is a constant or a variable that is new or
already recorded. -/
theorem rational_value (u q : ℤ) (s : BuildState) :
    (∃ c, (rational u q s).1 = C c) ∨
      ∃ i, (rational u q s).1 = X i ∧ (i = s.next ∨ ∃ e ∈ s.globals, e.1 = i) := by
  unfold rational
  dsimp only
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · split
    · rename_i e he
      exact Or.inr ⟨e.1, rfl, Or.inr ⟨e, List.mem_of_find?_eq_some he, rfl⟩⟩
    · exact Or.inr ⟨s.next, rfl, Or.inl rfl⟩

theorem wp_rational {G : ℕ → Prop} {u q : ℤ} {K : Poly → BuildState → Prop}
    (hs : (normalize u q).2 = 1 ∨
      (s.globals.find? fun e => e.2 == normalize u q).isSome = true ∨ G s.next)
    (hgl : ∀ e ∈ s.globals, G e.1)
    (h : ∀ v, VarsIn v G → K v (rational u q s).2) : WP (rational u q) s K := by
  refine h _ ?_
  unfold rational
  dsimp only
  split_ifs with h1
  · exact VarsIn.C _ G
  · split
    · rename_i e he
      exact VarsIn.X (hgl e (List.mem_of_find?_eq_some he))
    · rename_i hn
      rcases hs with hs | hs | hs
      · exact absurd hs h1
      · rw [hn] at hs; exact absurd hs (by simp)
      · exact VarsIn.X hs

theorem wp_gen {K : Code → BuildState → Prop}
    (h : WP (rational 1641 8) s fun c1 s1 => WP (rational (-15465) 4) s1 fun c2 s2 =>
      WP (rational 87483 32) s2 fun c3 s3 => K ![0, c1, -145, c2, c3] s3) : WP gen s K := h

/-- Weakening of the postcondition. -/
theorem WP.mono {b : Build α} {K K' : α → BuildState → Prop} (h : WP b s K)
    (hK : ∀ a s', K a s' → K' a s') : WP b s K' := hK _ _ h

/-! ### Loops -/

/-- Run `f` on the members of a list in order and collect the results. -/
def mapL {γ : Type} (f : γ → Build α) : List γ → Build (List α)
  | [] => pure []
  | a :: l => do
    let b ← f a
    let bs ← mapL f l
    pure (b :: bs)

@[simp] theorem mapL_nil {γ : Type} (f : γ → Build α) : mapL f [] = pure [] := rfl

theorem mapL_cons {γ : Type} (f : γ → Build α) (a : γ) (l : List γ) :
    mapL f (a :: l) = (do let b ← f a; let bs ← mapL f l; pure (b :: bs)) := rfl

/-- The value of `mapL` has the same length as the list. -/
theorem length_mapL {γ : Type} (f : γ → Build α) (l : List γ) (s : BuildState) :
    (mapL f l s).1.length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    show (mapL f l (f a s).2).1.length + 1 = l.length + 1
    rw [ih]

end Build

/-! ### Points, pairs and call arguments -/

/-- The point `(X_k, …, X_{k+4})` of consecutive variables (a parameter point). -/
noncomputable def varPoint (k : ℕ) : Code := fun i => X (k + i)

/-- The pair `(X_k, X_{k+1})`. -/
noncomputable def varPair (k : ℕ) : Pair := (X k, X (k + 1))

/-- A pair as a parameter list of length two. -/
noncomputable def Pair.args (u : Pair) : Fin 2 → Poly := ![u.1, u.2]

/-- A fresh pair: two fresh variables. -/
noncomputable def Build.freshPair : Build Pair := do
  let a ← Build.fresh
  let b ← Build.fresh
  pure (a, b)

@[simp] theorem Build.freshPair_apply (s : BuildState) :
    Build.freshPair s = ((X s.next, X (s.next + 1)), { s with next := s.next + 2 }) := rfl

namespace ArgsIn

variable {G : ℕ → Prop}

theorem append {m n : ℕ} {a : Fin m → Poly} {b : Fin n → Poly} (ha : ArgsIn a G)
    (hb : ArgsIn b G) : ArgsIn (Fin.append a b) G := by
  intro k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]; exact ha i
  · rw [Fin.append_right]; exact hb i

theorem code {p : Code} (hp : CodeIn p G) : ArgsIn p G := hp

theorem pair {u : Pair} (hu : PairIn u G) : ArgsIn u.args G := by
  intro k
  fin_cases k
  exacts [hu.1, hu.2]

theorem single {a : Poly} (ha : VarsIn a G) : ArgsIn ![a] G := by
  intro k
  fin_cases k
  exact ha

theorem nil : ArgsIn ![] G := fun k => k.elim0

theorem cons {n : ℕ} {a : Poly} {v : Fin n → Poly} (ha : VarsIn a G) (hv : ArgsIn v G) :
    ArgsIn (Matrix.vecCons a v) G := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [Matrix.cons_val_zero]; exact ha
  · rw [Matrix.cons_val_succ]; exact hv i

end ArgsIn

theorem CodeIn.varPoint {G : ℕ → Prop} {k : ℕ} (h : ∀ i : Fin 5, G (k + i)) :
    CodeIn (varPoint k) G := fun i => VarsIn.X (h i)

theorem PairIn.varPair {G : ℕ → Prop} {k : ℕ} (h0 : G k) (h1 : G (k + 1)) :
    PairIn (varPair k) G := ⟨VarsIn.X h0, VarsIn.X h1⟩

namespace Build

variable {s : BuildState}

theorem wp_freshIdx {G : ℕ → Prop} {K : ℕ → BuildState → Prop} (hs : G s.next)
    (h : ∀ k, G k → K k { s with next := s.next + 1 }) : WP freshIdx s K :=
  h _ hs

theorem wp_freshPair {G : ℕ → Prop} {K : Pair → BuildState → Prop} (h0 : G s.next)
    (h1 : G (s.next + 1)) (h : ∀ u, PairIn u G → K u { s with next := s.next + 2 }) :
    WP freshPair s K :=
  h _ ⟨VarsIn.X h0, VarsIn.X h1⟩

end Build

/-! ### Blocks of fresh points and pairs -/

/-- A fresh point: the five next variables `(X_c, …, X_{c+4})` (the allocation of
`Build.freshPoint`, returned as `varPoint c`). -/
noncomputable def Build.point : Build Code := fun s => (varPoint s.next, { s with next := s.next + 5 })

/-- `n` fresh points: the `5n` next variables, point by point. -/
noncomputable def Build.freshPoints (n : ℕ) : Build (Fin n → Code) := fun s =>
  (fun i j => X (s.next + 5 * i + j), { s with next := s.next + 5 * n })

/-- `n` fresh pairs: the `2n` next variables, pair by pair. -/
noncomputable def Build.freshPairs (n : ℕ) : Build (Fin n → Pair) := fun s =>
  (fun i => (X (s.next + 2 * i), X (s.next + 2 * i + 1)), { s with next := s.next + 2 * n })

/-- The parameter list `(X_k, …, X_{k+n-1})`. -/
noncomputable def varArgs (k n : ℕ) : Fin n → Poly := fun i => X (k + i)

/-- The coordinates of `n` points as one parameter list. -/
noncomputable def codesArgs {n : ℕ} (C : Fin n → Code) : Fin (n * 5) → Poly := fun k =>
  C ⟨k / 5, Nat.div_lt_of_lt_mul (by have := k.isLt; linarith)⟩ ⟨k % 5, Nat.mod_lt _ (by omega)⟩

/-- The components of `n` pairs as one parameter list. -/
noncomputable def pairsArgs {n : ℕ} (D : Fin n → Pair) : Fin (n * 2) → Poly := fun k =>
  if k.val % 2 = 0 then
    (D ⟨k / 2, Nat.div_lt_of_lt_mul (by have := k.isLt; linarith)⟩).1
  else (D ⟨k / 2, Nat.div_lt_of_lt_mul (by have := k.isLt; linarith)⟩).2

namespace ArgsIn

variable {G : ℕ → Prop}

theorem bind₁ {n : ℕ} {f : Fin n → Poly} {P : MvPolynomial (Fin n) ℤ} (h : ArgsIn f G) :
    VarsIn (MvPolynomial.bind₁ f P) G := VarsIn.bind₁ h

theorem varArgs {k n : ℕ} (h : ∀ i : Fin n, G (k + i)) : ArgsIn (ZInQ.Syntax.varArgs k n) G :=
  fun i => VarsIn.X (h i)

theorem codes {n : ℕ} {C : Fin n → Code} (h : ∀ i, CodeIn (C i) G) : ArgsIn (codesArgs C) G :=
  fun _ => h _ _

theorem pairs {n : ℕ} {D : Fin n → Pair} (h : ∀ i, PairIn (D i) G) : ArgsIn (pairsArgs D) G := by
  intro k
  unfold pairsArgs
  split_ifs
  exacts [(h _).1, (h _).2]

end ArgsIn

namespace Build

variable {s : BuildState}

theorem wp_point {G : ℕ → Prop} {K : Code → BuildState → Prop}
    (hs : ∀ i < 5, G (s.next + i))
    (h : ∀ p, CodeIn p G → K p { s with next := s.next + 5 }) : WP point s K :=
  h _ fun i => VarsIn.X (hs _ i.isLt)

theorem wp_freshPoints {G : ℕ → Prop} {n : ℕ} {K : (Fin n → Code) → BuildState → Prop}
    (hs : ∀ i < 5 * n, G (s.next + i))
    (h : ∀ ps, (∀ i, CodeIn (ps i) G) → K ps { s with next := s.next + 5 * n }) :
    WP (freshPoints n) s K := by
  refine h _ fun i j => VarsIn.X ?_
  rw [add_assoc]
  exact hs _ (by have := i.isLt; have := j.isLt; omega)

theorem wp_freshPairs {G : ℕ → Prop} {n : ℕ} {K : (Fin n → Pair) → BuildState → Prop}
    (hs : ∀ i < 2 * n, G (s.next + i))
    (h : ∀ us, (∀ i, PairIn (us i) G) → K us { s with next := s.next + 2 * n }) :
    WP (freshPairs n) s K := by
  refine h _ fun i => ⟨VarsIn.X (hs _ (by have := i.isLt; omega)), VarsIn.X ?_⟩
  rw [add_assoc]
  exact hs _ (by have := i.isLt; omega)

end Build

/-! ### Values of call arguments -/

@[simp] theorem ev_varPoint (y : ℕ → ℚ) (k : ℕ) (i : Fin 5) : ev y (varPoint k i) = y (k + i) :=
  ev_X _ _

@[simp] theorem ev_varPair_fst (y : ℕ → ℚ) (k : ℕ) : ev y (varPair k).1 = y k := ev_X _ _

@[simp] theorem ev_varPair_snd (y : ℕ → ℚ) (k : ℕ) : ev y (varPair k).2 = y (k + 1) := ev_X _ _

@[simp] theorem ev_varArgs (y : ℕ → ℚ) (k n : ℕ) (i : Fin n) : ev y (varArgs k n i) = y (k + i) :=
  ev_X _ _

/-- The values of concatenated parameter lists are the concatenated values. -/
theorem ev_comp_append (y : ℕ → ℚ) {m n : ℕ} (f : Fin m → Poly) (g : Fin n → Poly) :
    (fun k => ev y (Fin.append f g k)) = Fin.append (fun k => ev y (f k)) (fun k => ev y (g k)) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-! ### Constructed templates -/

/-- **Well-formedness from the scope facts.** If the final formula of a construction has the
scope facts for indices below the final counter, and the constant variables are below it, the
template is well formed. -/
theorem Build.template_wf_of_fok (p : ℕ) (b : Build Formula) {G : ℕ → Prop}
    (hG : ∀ i, G i → i < (b ⟨p, []⟩).2.next) (hp : p ≤ (b ⟨p, []⟩).2.next)
    (hgl : ∀ e ∈ (b ⟨p, []⟩).2.globals, e.1 < (b ⟨p, []⟩).2.next)
    (hφ : FOk G (b ⟨p, []⟩).2.next (b ⟨p, []⟩).1) : (Build.template p b).WF :=
  Build.template_wf p b hp hgl (varsLT_compile_of_fok hφ hG)

/-- The formula `⋀(E_1, …, E_r, φ)` of a constructed template. -/
noncomputable def Build.fullFormula (p : ℕ) (b : Build Formula) : Formula :=
  .and ((b ⟨p, []⟩).2.globals.map globalEq ++ [(b ⟨p, []⟩).1])

theorem Build.template_poly (p : ℕ) (b : Build Formula) :
    (Build.template p b).poly = (Build.fullFormula p b).compile := rfl

/-- **Relations of constructed templates through private blocks.** Let the final formula `φ`
of a construction have the scope facts for the indices `Avail N B`, where `B` is the list of
its call blocks, let these blocks be pairwise disjoint and lie above the parameters, and let
the constant variables be available. Then `Rel(a)` holds exactly when some assignment extending
`a` gives every constant variable its value and satisfies `φ^*`, the formula with every call
atom replaced by the callee relation. -/
theorem Build.template_rel_iff_lift (p : ℕ) (b : Build Formula) {N : ℕ} {B : List (ℕ × ℕ)}
    (hN : (b ⟨p, []⟩).2.next = N) (hB : (b ⟨p, []⟩).1.blocks = B)
    (hdisj : B.Pairwise BlockDisjoint) (hp : ∀ bl ∈ B, p ≤ bl.1)
    (hgl : ∀ e ∈ (b ⟨p, []⟩).2.globals, Avail N B e.1 ∧ e.2.2 ≠ 0)
    (hφ : FOk (Avail N B) N (b ⟨p, []⟩).1) (hpN : p ≤ N) (a : Fin p → ℚ) :
    (Build.template p b).Rel a ↔
      ∃ y : ℕ → ℚ, (∀ i : Fin p, y i = a i) ∧
        (∀ e ∈ (b ⟨p, []⟩).2.globals, y e.1 = e.2.1 / e.2.2) ∧ (b ⟨p, []⟩).1.Lift y := by
  set φ := (b ⟨p, []⟩).1 with hφdef
  set gl := (b ⟨p, []⟩).2.globals with hgldef
  have hG : ∀ i, Avail N B i → i < N := fun i h => h.1
  have hwf : (Build.template p b).WF :=
    Build.template_wf_of_fok p b (G := Avail N B) (by rw [hN]; exact hG) (by rw [hN]; exact hpN)
      (fun e he => by rw [hN]; exact (hgl e he).1.1) (by rw [hN]; exact hφ)
  have hglobals : ∀ e ∈ gl, FOk (Avail N B) N (globalEq e) := fun e he => by
    unfold globalEq
    exact FOk.eq ((VarsIn.C _ _).mul (VarsIn.X (hgl e he).1)) (VarsIn.C _ _)
  have hψ : FOk (Avail N B) N (Build.fullFormula p b) :=
    FOk.and_iff.2 fun ψ hψ => by
      rcases List.mem_append.1 hψ with h | h
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
        exact hglobals e he
      · rw [List.mem_singleton] at h
        exact h ▸ hφ
  have hblocks : (Build.fullFormula p b).blocks = B := by
    simp only [Build.fullFormula, Formula.blocks_and, List.flatMap_append, List.flatMap_map,
      List.flatMap_singleton]
    rw [← hφdef, hB]
    have : gl.flatMap (fun e => (globalEq e).blocks) = [] := by
      simp [globalEq, Formula.blocks]
    rw [← hgldef, this, List.nil_append]
  have hscoped : (Build.fullFormula p b).Scoped :=
    ⟨hψ.1, hblocks ▸ hdisj, fun f hf i hi => by
      rw [hblocks, ← blockFree_iff]
      exact (hψ.2.1 f hf i hi).2⟩
  refine (ExPoly.rel_iff_exists_lift hwf (Build.template_poly p b) hscoped
    (by rw [hblocks]; exact hp) a).trans ?_
  refine exists_congr fun y => and_congr_right fun _ => ?_
  simp only [Build.fullFormula, Formula.lift_and, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_singleton]
  refine and_congr_left' (forall₂_congr fun e he => ?_)
  rw [globalEq, Formula.lift_eq, eq_div_iff (by exact_mod_cast (hgl e he).2)]
  simp [mul_comm]

/-- Pairwise disjointness of blocks from a decidable sufficient condition. -/
def blocksSep (B : List (ℕ × ℕ)) : Prop :=
  B.Pairwise fun b b' => b.1 + b.2 ≤ b'.1 ∨ b'.1 + b'.2 ≤ b.1 ∨ b.2 = 0 ∨ b'.2 = 0

instance (B : List (ℕ × ℕ)) : Decidable (blocksSep B) := inferInstanceAs (Decidable (List.Pairwise _ _))

theorem pairwise_blockDisjoint_of_sep {B : List (ℕ × ℕ)} (h : blocksSep B) :
    B.Pairwise BlockDisjoint :=
  h.imp fun {b b'} hbb' i hi hi' => by
    unfold InBlock at hi hi'
    omega


/-- The facts established for a constructed template with `p` parameters: the final counter
`N`, the list `B` of its call blocks (separated and above the parameters), the list `GE` of the
global equations of its rational constants, and the scope facts of the final formula for the
indices `Avail N B`. -/
structure Build.Facts (p : ℕ) (b : Build Formula) (N : ℕ) (B : List (ℕ × ℕ))
    (GE : List (ℕ × ℤ × ℤ)) : Prop where
  next : (b ⟨p, []⟩).2.next = N
  blocks : (b ⟨p, []⟩).1.blocks = B
  globalsEq : (b ⟨p, []⟩).2.globals = GE
  sep : blocksSep B
  above : ∀ bl ∈ B, p ≤ bl.1
  le : p ≤ N
  globals : ∀ e ∈ GE, Avail N B e.1 ∧ e.2.2 ≠ 0
  fok : FOk (Avail N B) N (b ⟨p, []⟩).1

namespace Build.Facts

variable {p : ℕ} {b : Build Formula} {N : ℕ} {B : List (ℕ × ℕ)} {GE : List (ℕ × ℤ × ℤ)}

/-- The facts from one weakest-precondition run. -/
theorem of_wp (h : Build.WP b ⟨p, []⟩ fun φ s => FOk (Avail N B) N φ ∧ φ.blocks = B ∧
      s.next = N ∧ s.globals = GE)
    (sep : blocksSep B) (above : ∀ bl ∈ B, p ≤ bl.1) (le : p ≤ N)
    (globals : ∀ e ∈ GE, Avail N B e.1 ∧ e.2.2 ≠ 0) : Build.Facts p b N B GE :=
  ⟨h.2.2.1, h.2.1, h.2.2.2, sep, above, le, globals, h.1⟩

theorem witnesses (h : Build.Facts p b N B GE) : (Build.template p b).witnesses = N - p := by
  show (b ⟨p, []⟩).2.next - p = N - p
  rw [h.next]

theorem wf (h : Build.Facts p b N B GE) : (Build.template p b).WF :=
  Build.template_wf_of_fok p b (G := Avail N B) (by rw [h.next]; exact fun i hi => hi.1)
    (by rw [h.next]; exact h.le)
    (fun e he => by rw [h.next]; rw [h.globalsEq] at he; exact (h.globals e he).1.1)
    (by rw [h.next]; exact h.fok)

/-- The relation of a template with the facts, through its private blocks: some assignment
extending the parameters gives every constant variable its value and satisfies the final
formula with every call replaced by the callee relation. -/
theorem rel_iff (h : Build.Facts p b N B GE) (a : Fin p → ℚ) :
    (Build.template p b).Rel a ↔
      ∃ y : ℕ → ℚ, (∀ i : Fin p, y i = a i) ∧
        (∀ e ∈ GE, y e.1 = e.2.1 / e.2.2) ∧ (b ⟨p, []⟩).1.Lift y := by
  rw [← h.globalsEq]
  exact Build.template_rel_iff_lift p b h.next h.blocks (pairwise_blockDisjoint_of_sep h.sep)
    h.above (h.globalsEq ▸ h.globals) h.fok h.le a

/-- The relation of a template with the facts and without rational constants. -/
theorem rel_iff_nil (h : Build.Facts p b N B []) (a : Fin p → ℚ) :
    (Build.template p b).Rel a ↔
      ∃ y : ℕ → ℚ, (∀ i : Fin p, y i = a i) ∧ (b ⟨p, []⟩).1.Lift y := by
  rw [h.rel_iff]
  simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, true_and]

end Build.Facts

end ZInQ.Syntax

/-! ### Tactics -/

namespace ZInQ.Syntax.Build

open Lean Elab Tactic Meta

/-- The lemma applied by `scope` to a goal, by the head of the goal and of its subject. -/
def scopeLemma (tgt : Expr) : MetaM (Option Name) := do
  let fn := tgt.getAppFn
  let args := tgt.getAppArgs
  let sub (k : ℕ) : MetaM Expr := whnfCore args[k]!
  match fn.constName? with
  | some ``FOk =>
    let φ ← sub 2
    match φ.getAppFn.constName? with
    | some ``Formula.and =>
      let l ← whnfR φ.appArg!
      match l.getAppFn.constName? with
      | some ``List.cons => pure ``FOk.and_cons
      | some ``List.nil => pure ``FOk.and_nil
      | some ``HAppend.hAppend => pure ``FOk.and_append
      | _ => pure none
    | some ``Formula.or =>
      let l ← whnfR φ.appArg!
      match l.getAppFn.constName? with
      | some ``List.cons => pure ``FOk.or_cons
      | some ``List.nil => pure ``FOk.or_nil
      | _ => pure none
    | some ``Formula.eq => pure ``FOk.eq
    | some ``Formula.atom => pure ``FOk.atom
    | some ``feq => pure ``FOk.feq
    | some ``peq => pure ``FOk.peq
    | some ``isO => pure ``FOk.isO
    | some ``fin => pure ``FOk.fin
    | some ``curve => pure ``FOk.curve
    | some ``nzFormula => pure ``FOk.nzFormula
    | some ``zFormula => pure ``FOk.zFormula
    | some ``ixFormula => pure ``FOk.ixFormula
    | some ``divFormula => pure ``FOk.divFormula
    | some ``posFormula => pure ``FOk.posFormula
    | _ => pure none
  | some ``PairIn =>
    let u ← sub 0
    match u.getAppFn.constName? with
    | some ``Pair.mul => pure ``PairIn.mul
    | some ``Pair.sq => pure ``PairIn.sq
    | some ``Pair.add => pure ``PairIn.add
    | some ``Pair.sub => pure ``PairIn.sub
    | some ``Pair.neg => pure ``PairIn.neg
    | some ``Pair.smul => pure ``PairIn.smul
    | some ``Pair.conj => pure ``PairIn.conj
    | some ``Pair.pow => pure ``PairIn.pow
    | some ``Pair.one => pure ``PairIn.one
    | some ``Pair.zero => pure ``PairIn.zero
    | some ``Pair.A => pure ``PairIn.A
    | some ``Pair.delta => pure ``PairIn.delta
    | some ``Pair.ofInt => pure ``PairIn.ofInt
    | some ``Prod.mk => pure ``PairIn.mk
    | some ``varPair => pure ``PairIn.varPair
    | some ``Code.x => pure ``CodeIn.x
    | some ``Code.y => pure ``CodeIn.y
    | _ => pure none
  | some ``CodeIn =>
    let p ← sub 0
    match p.getAppFn.constName? with
    | some ``varPoint => pure ``CodeIn.varPoint
    | some ``Code.neg => pure ``CodeIn.neg
    | some ``Code.O => pure ``CodeIn.O
    | some ``Matrix.vecCons => pure ``CodeIn.mk
    | _ => pure none
  | some ``ArgsIn =>
    let g ← sub 1
    match g.getAppFn.constName? with
    | some ``Fin.append => pure ``ArgsIn.append
    | some ``Pair.args => pure ``ArgsIn.pair
    | some ``Matrix.vecCons => pure ``ArgsIn.cons
    | some ``Matrix.vecEmpty => pure ``ArgsIn.nil
    | some ``varArgs => pure ``ArgsIn.varArgs
    | some ``codesArgs => pure ``ArgsIn.codes
    | some ``pairsArgs => pure ``ArgsIn.pairs
    | _ => pure ``ArgsIn.code
  | some ``VarsIn =>
    let f ← sub 0
    match f.getAppFn.constName? with
    | some ``HAdd.hAdd => pure ``VarsIn.add
    | some ``HMul.hMul => pure ``VarsIn.mul
    | some ``HSub.hSub => pure ``VarsIn.sub
    | some ``Neg.neg => pure ``VarsIn.neg
    | some ``HPow.hPow => pure ``VarsIn.pow
    | some ``MvPolynomial.X => pure ``VarsIn.X
    | some ``MvPolynomial.C => pure ``VarsIn.C
    | some ``Int.cast => pure ``VarsIn.intCast
    | some ``Pair.norm => pure ``PairIn.norm
    | some ``MvPolynomial.bind₁ => pure ``ArgsIn.bind₁
    | some ``DFunLike.coe =>
      if f.getAppNumArgs == 6 && (f.getArg! 4).isAppOf ``MvPolynomial.bind₁ then
        pure ``ArgsIn.bind₁
      else if f.getAppNumArgs == 6 && (f.getArg! 4).isAppOf ``MvPolynomial.C then
        pure ``VarsIn.C
      else pure none
    | some ``OfNat.ofNat =>
      match f.getAppArgs[1]!.rawNatLit? with
      | some 0 => pure ``VarsIn.zero
      | some 1 => pure ``VarsIn.one
      | _ => pure ``VarsIn.ofNat
    | some ``Zero.zero => pure ``VarsIn.zero
    | some ``One.one => pure ``VarsIn.one
    | _ => pure none
  | _ => pure none

/-- The recursion depth allowed to `scope`: far beyond the depth of any goal it meets. -/
def scopeFuel : ℕ := 100000

/-- Prove a scope goal (`FOk`, `PairIn`, `CodeIn`, `ArgsIn`, `VarsIn`, an index predicate) by
the structural lemmas, the hypotheses, unfolding of definitions and `decide`. -/
def scopeGoal : ℕ → MVarId → TacticM Unit
  | 0, _ => throwError "scope: recursion limit reached"
  | fuel + 1, g => g.withContext do
    let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations.headBeta
    if (← observing? (withReducible g.assumption)).isSome then return
    -- a universally quantified hypothesis `∀ i, P (f i)`
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).cleanupAnnotations
      if ty.isForall then
        if !(← isProp ty.bindingDomain!) then
          let saved ← saveState
          try
            let gs ← withReducible (g.apply d.toExpr)
            for g' in gs do
              unless ← g'.isAssigned do scopeGoal fuel g'
            return
          catch _ => saved.restore
    -- a goal `∀ i : Fin n, P i`
    if tgt.isForall && (tgt.bindingDomain!.isAppOf ``Fin) then
      let saved ← getGoals
      setGoals [g]
      evalTactic (← `(tactic| (intro i; fin_cases i)))
      let gs ← getGoals
      setGoals saved
      for g' in gs do scopeGoal fuel g'
      return
    match ← scopeLemma tgt with
    | some n =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels n)
      for g' in gs do
        unless ← g'.isAssigned do scopeGoal fuel g'
    | none =>
      let args := tgt.getAppArgs
      let fn := tgt.getAppFn
      -- coordinates `(e).1`, `(e).2` of a pair and `p i` of a code
      if fn.isConstOf ``VarsIn then
        let f ← whnfCore args[0]!
        if f.isAppOfArity ``Prod.fst 3 || f.isAppOfArity ``Prod.snd 3 then
          let u := f.appArg!
          let G := args[1]!
          let h ← mkFreshExprMVar (mkApp2 (mkConst ``PairIn) u G)
          scopeGoal fuel h.mvarId!
          let pf ← if f.isAppOfArity ``Prod.fst 3 then mkAppM ``And.left #[h]
            else mkAppM ``And.right #[h]
          g.assign pf
          return
        let fType ← inferType f.getAppFn
        if f.isApp && (← isDefEq fType (← mkArrow (mkApp (mkConst ``Fin) (mkNatLit 5))
            (mkConst ``ZInQ.Syntax.Poly))) then
          let p := f.appFn!
          let G := args[1]!
          let h ← mkFreshExprMVar (mkApp2 (mkConst ``CodeIn) p G)
          scopeGoal fuel h.mvarId!
          g.assign (mkApp h f.appArg!)
          return
      -- unfold a user definition at the head of the subject
      let subIdx? : Option ℕ :=
        if fn.isConstOf ``FOk then some 2
        else if fn.isConstOf ``PairIn || fn.isConstOf ``CodeIn || fn.isConstOf ``VarsIn then some 0
        else none
      if let some k := subIdx? then
        let e ← whnfCore args[k]!
        if let some e' ← unfoldDefinition? e then
          let tgt' := mkAppN fn (args.set! k e')
          let g' ← g.replaceTargetDefEq tgt'
          scopeGoal fuel g'
          return
      -- numeric index conditions
      let saved ← getGoals
      setGoals [g]
      try
        evalTactic (← `(tactic| decide))
      catch _ =>
        setGoals saved
        throwError "scope: cannot prove{indentExpr tgt}"
      setGoals saved

/-- Prove scope goals (`FOk`, `PairIn`, `CodeIn`, `ArgsIn`, `VarsIn`, index predicates). -/
elab "scope" : tactic => do
  let g ← getMainGoal
  setGoals []
  scopeGoal scopeFuel g

/-- One step of a weakest-precondition computation `WP b s K`: dispatch on the head of `b`. -/
elab "wp_step " G:term:max N:term:max : tactic => do
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations.headBeta
  let some (b, _) := (do
      guard (tgt.isAppOfArity ``Build.WP 4)
      pure (tgt.getArg! 1, ())) | throwError "wp_step: the goal is not a `WP` statement{indentExpr tgt}"
  let b ← whnfCore b
  let tac ← match b.getAppFn.constName? with
    | some ``Bind.bind => `(tactic| refine Build.wp_bind ?_)
    | some ``Pure.pure => `(tactic| refine Build.wp_pure ?_)
    | some ``Build.fresh => `(tactic| refine Build.wp_fresh (G := $G) (by decide) fun _ _ => ?_)
    | some ``Build.freshIdx => `(tactic| refine Build.wp_freshIdx (G := $G) (by decide) fun _ _ => ?_)
    | some ``Build.freshPair =>
      `(tactic| refine Build.wp_freshPair (G := $G) (by decide) (by decide) fun _ _ => ?_)
    | some ``Build.freshPoint =>
      `(tactic| refine Build.wp_freshPoint (G := $G) (by decide) (by decide) (by decide) (by decide)
        (by decide) fun _ _ => ?_)
    | some ``Build.point =>
      `(tactic| refine Build.wp_point (G := $G) (by decide) fun _ _ => ?_)
    | some ``Build.freshPoints =>
      `(tactic| refine Build.wp_freshPoints (G := $G) (by decide) fun _ _ => ?_)
    | some ``Build.freshPairs =>
      `(tactic| refine Build.wp_freshPairs (G := $G) (by decide) fun _ _ => ?_)
    | some ``Build.call =>
      `(tactic| refine Build.wp_call (G := $G) (N := $N) (by assumption) (by assumption) (by scope) (by decide)
        fun _ _ _ => ?_)
    | some ``Build.nz => `(tactic| refine Build.wp_nz (G := $G) (N := $N) (by decide) (by scope) fun _ _ _ => ?_)
    | some ``Build.fnz => `(tactic| refine Build.wp_fnz (G := $G) (N := $N) (by decide) (by scope) fun _ _ _ => ?_)
    | some ``Build.pos =>
      `(tactic| refine Build.wp_pos (G := $G) (N := $N) (by decide) (by decide) (by decide) (by decide) (by scope)
        fun _ _ _ => ?_)
    | some ``Build.fdiv =>
      `(tactic| refine Build.wp_fdiv (G := $G) (N := $N) (by decide) (by decide) (by decide) (by scope) (by scope)
        fun _ _ _ _ _ => ?_)
    | some ``Build.zGadget =>
      `(tactic| refine Build.wp_zGadget (G := $G) (N := $N) (by decide) (by scope) (by scope)
        fun _ _ _ => ?_)
    | some ``Build.gen => `(tactic| refine Build.wp_gen ?_)
    | some ``Build.rational =>
      `(tactic| refine Build.wp_rational (G := $G) (by decide) (by decide) fun _ _ => ?_)
    | some ``Build.mapL => `(tactic| first | rw [Build.mapL_cons] | rw [Build.mapL_nil])
    | some n => `(tactic| unfold $(mkIdent n):ident)
    | none => throwError "wp_step: unknown program{indentExpr b}"
  evalTactic tac

end ZInQ.Syntax.Build

/-- Run `wp_step` until the program is consumed. -/
macro "wp_run " G:term:max N:term:max : tactic => `(tactic| repeat wp_step $G $N)

/-- Close the final goal of a weakest-precondition run for `Build.Facts.of_wp`. -/
macro "facts_close" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_⟩
  · scope
  · try dsimp only
    first
    | (simp only [ZInQ.Syntax.Formula.blocks_and, ZInQ.Syntax.Formula.blocks_or,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
        List.cons_append, List.singleton_append, ZInQ.Syntax.blocks_feq, ZInQ.Syntax.blocks_fin,
        ZInQ.Syntax.blocks_peq, ZInQ.Syntax.blocks_isO, ZInQ.Syntax.blocks_nzFormula,
        ZInQ.Syntax.blocks_posFormula, ZInQ.Syntax.blocks_curve, ZInQ.Syntax.blocks_zFormula,
        ZInQ.Syntax.blocks_ixFormula, ZInQ.Syntax.blocks_divFormula, ZInQ.Syntax.Formula.blocks,
        *] <;> decide)
    | decide
  · decide
  · decide))
