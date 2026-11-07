import Mathlib

/-!
# Tape lists

Finite lists of naturals are coded by `nil = 0` and `cons h t = 2 ^ h * (2 * t + 1)`.
`cons` is a bijection from `ℕ × ℕ` onto the positive naturals, every natural codes exactly one
list, and `listGet`/`listSet` on codes satisfy the read-after-write equations. A register file
`ρ` is represented by a code `L` when `ρ i = listGet L i` for every `i`.

(Blueprint: `compiler/natural/universal/tape-lists.md`.)
-/

namespace ZInQ.Compiler.Universal

/-- `cons h t = 2 ^ h * (2 * t + 1)`. -/
def cons (h t : ℕ) : ℕ := 2 ^ h * (2 * t + 1)

/-- Head and tail of a code: the number of halvings until odd, and `(x / 2 ^ h - 1) / 2`;
`uncons 0 = (0, 0)`. -/
def uncons (x : ℕ) : ℕ × ℕ := (padicValNat 2 x, (x / 2 ^ padicValNat 2 x - 1) / 2)

theorem cons_pos (h t : ℕ) : 0 < cons h t := by unfold cons; positivity

theorem cons_ne_zero (h t : ℕ) : cons h t ≠ 0 := (cons_pos h t).ne'

@[simp] theorem uncons_zero : uncons 0 = (0, 0) := by simp [uncons]

@[simp] theorem uncons_cons (h t : ℕ) : uncons (cons h t) = (h, t) := by
  have hv : padicValNat 2 (cons h t) = h := by
    rw [cons, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by omega), add_zero]
  unfold uncons
  rw [hv, cons, Nat.mul_div_cancel_left _ (by positivity)]
  congr 1
  omega

theorem cons_uncons {x : ℕ} (hx : 0 < x) : cons (uncons x).1 (uncons x).2 = x := by
  obtain ⟨h, m, ⟨t, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := x) hx.ne'
  have : 2 ^ h * (2 * t + 1) = cons h t := rfl
  rw [this, uncons_cons]

theorem cons_inj {h t h' t' : ℕ} : cons h t = cons h' t' ↔ h = h' ∧ t = t' := by
  constructor
  · intro e
    have := congrArg uncons e
    simp only [uncons_cons, Prod.mk.injEq] at this
    exact this
  · rintro ⟨rfl, rfl⟩; rfl

/-- `cons` is a bijection from `ℕ × ℕ` onto the positive naturals. -/
theorem cons_bijective :
    Function.Bijective (fun p : ℕ × ℕ => (⟨cons p.1 p.2, cons_pos _ _⟩ : {x : ℕ // 0 < x})) := by
  refine ⟨fun p q e => ?_, fun x => ⟨uncons x.1, Subtype.ext (cons_uncons x.2)⟩⟩
  have := congrArg (fun x : {x : ℕ // 0 < x} => uncons x.1) e
  simpa using this

theorem tail_lt_cons (h t : ℕ) : t < cons h t := by
  unfold cons
  have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  nlinarith

theorem head_lt_cons (h t : ℕ) : h < cons h t := by
  unfold cons
  have : h < 2 ^ h := Nat.lt_two_pow_self
  nlinarith

theorem uncons_snd_lt {x : ℕ} (hx : 0 < x) : (uncons x).2 < x := by
  conv_rhs => rw [← cons_uncons hx]
  exact tail_lt_cons _ _

theorem uncons_fst_lt {x : ℕ} (hx : 0 < x) : (uncons x).1 < x := by
  conv_rhs => rw [← cons_uncons hx]
  exact head_lt_cons _ _

/-! ### Lists -/

/-- The code of a list. -/
def listCode : List ℕ → ℕ
  | [] => 0
  | h :: t => cons h (listCode t)

/-- The list coded by a natural number. -/
def decodeList (x : ℕ) : List ℕ :=
  if _hx : x = 0 then [] else (uncons x).1 :: decodeList (uncons x).2
termination_by x
decreasing_by exact uncons_snd_lt (Nat.pos_of_ne_zero ‹x ≠ 0›)

theorem decodeList_zero : decodeList 0 = [] := by
  rw [decodeList]; simp

theorem decodeList_cons (h t : ℕ) : decodeList (cons h t) = h :: decodeList t := by
  rw [decodeList]; simp [cons_ne_zero]

theorem decodeList_listCode (l : List ℕ) : decodeList (listCode l) = l := by
  induction l with
  | nil => exact decodeList_zero
  | cons h t ih => rw [listCode, decodeList_cons, ih]

theorem listCode_decodeList (x : ℕ) : listCode (decodeList x) = x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [decodeList_zero]; rfl
    · rw [← cons_uncons hx, decodeList_cons, listCode, ih _ (by
        conv_rhs => rw [← cons_uncons hx]
        exact tail_lt_cons _ _)]

/-- Every natural number codes exactly one finite list. -/
theorem listCode_bijective : Function.Bijective listCode :=
  Function.bijective_iff_has_inverse.mpr
    ⟨decodeList, decodeList_listCode, listCode_decodeList⟩

/-! ### Reading and writing entries -/

/-- `listGet L i`: the `i`-th entry of the list coded by `L`, or `0` past its end. -/
def listGet (L : ℕ) : ℕ → ℕ
  | 0 => (uncons L).1
  | i + 1 => listGet (uncons L).2 i

/-- `listSet L i v`: the list coded by `L` with entry `i` replaced by `v`, padded with zeros if it
is shorter. -/
def listSet (L : ℕ) : ℕ → ℕ → ℕ
  | 0, v => cons v (uncons L).2
  | i + 1, v => cons (uncons L).1 (listSet (uncons L).2 i v)

theorem listGet_zero_left (i : ℕ) : listGet 0 i = 0 := by
  induction i with
  | zero => simp [listGet]
  | succ i ih => simpa [listGet] using ih

@[simp] theorem listGet_cons_zero (h t : ℕ) : listGet (cons h t) 0 = h := by simp [listGet]

@[simp] theorem listGet_cons_succ (h t i : ℕ) : listGet (cons h t) (i + 1) = listGet t i := by
  simp [listGet]

@[simp] theorem listSet_cons_zero (h t v : ℕ) : listSet (cons h t) 0 v = cons v t := by
  simp [listSet]

@[simp] theorem listSet_cons_succ (h t i v : ℕ) :
    listSet (cons h t) (i + 1) v = cons h (listSet t i v) := by simp [listSet]

theorem listGet_listSet_self (L i v : ℕ) : listGet (listSet L i v) i = v := by
  induction i generalizing L with
  | zero => simp [listSet]
  | succ i ih => simp [listSet, ih]

theorem listGet_listSet_of_ne (L i i' v : ℕ) (h : i' ≠ i) :
    listGet (listSet L i v) i' = listGet L i' := by
  induction i generalizing L i' with
  | zero =>
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp [listSet, listGet]
  | succ i ih =>
    rcases i' with _ | i'
    · simp [listSet, listGet]
    · simp only [listSet, listGet_cons_succ]
      rw [ih _ _ (by omega), listGet]

/-- `listGet` on list codes is `List.getD`. -/
theorem listGet_listCode (l : List ℕ) (i : ℕ) : listGet (listCode l) i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [listCode, listGet_zero_left]
  | cons h t ih => cases i <;> simp [listCode, ih]

/-- Replace entry `i` of `l` by `v`, padding with zeros if `l` is shorter. -/
def listSetPad (l : List ℕ) (i v : ℕ) : List ℕ :=
  (l ++ List.replicate (i + 1 - l.length) 0).set i v

/-- `listSet` on list codes is `listSetPad`. -/
theorem listSet_listCode (l : List ℕ) (i v : ℕ) :
    listSet (listCode l) i v = listCode (listSetPad l i v) := by
  induction l generalizing i with
  | nil =>
    induction i with
    | zero => simp [listSetPad, listCode, listSet]
    | succ i ih =>
      simp only [listCode, listSet, uncons_zero] at ih ⊢
      rw [ih]
      simp [listSetPad, List.replicate_succ, listCode]
  | cons h t ih =>
    cases i with
    | zero => simp [listSetPad, listCode]
    | succ i =>
      simp only [listCode, listSet_cons_succ, ih]
      simp [listSetPad, listCode]

/-- A register file `ρ` is represented by the list code `L`. -/
def Represents (ρ : ℕ → ℕ) (L : ℕ) : Prop := ∀ i, ρ i = listGet L i

theorem Represents.update {ρ : ℕ → ℕ} {L : ℕ} (h : Represents ρ L) (i v : ℕ) :
    Represents (Function.update ρ i v) (listSet L i v) := by
  intro i'
  by_cases hi : i' = i
  · subst hi; rw [Function.update_self, listGet_listSet_self]
  · rw [Function.update_of_ne hi, listGet_listSet_of_ne _ _ _ _ hi, h]

/-! ### Saving and restoring a prefix -/

/-- Push the entries of the saved reversed prefix `s` back onto `r`. -/
def restore (s r : ℕ) : ℕ :=
  if _hs : s = 0 then r else restore (uncons s).2 (cons (uncons s).1 r)
termination_by s
decreasing_by exact uncons_snd_lt (Nat.pos_of_ne_zero ‹s ≠ 0›)

theorem restore_zero (r : ℕ) : restore 0 r = r := by rw [restore]; simp

theorem restore_cons (h s r : ℕ) : restore (cons h s) r = restore s (cons h r) := by
  rw [restore]; simp [cons_ne_zero]

theorem restore_of_ne_zero {s : ℕ} (hs : s ≠ 0) (r : ℕ) :
    restore s r = restore (uncons s).2 (cons (uncons s).1 r) := by
  rw [restore]; simp [hs]

/-- One step of the save loop: move the head of the list onto the saved prefix. -/
def saveStep (p : ℕ × ℕ) : ℕ × ℕ := ((uncons p.1).2, cons (uncons p.1).1 p.2)

/-- After `k` save steps, replacing the head and restoring the prefix sets entry `k`. -/
theorem restore_saveStep (v : ℕ) : ∀ (k L s : ℕ),
    restore (saveStep^[k] (L, s)).2 (listSet (saveStep^[k] (L, s)).1 0 v) =
      restore s (listSet L k v)
  | 0, L, s => rfl
  | k + 1, L, s => by
    rw [Function.iterate_succ_apply, saveStep]
    rw [restore_saveStep v k, restore_cons]
    rfl

end ZInQ.Compiler.Universal
