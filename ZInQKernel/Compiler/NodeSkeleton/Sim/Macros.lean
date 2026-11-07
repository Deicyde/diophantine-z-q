import ZInQKernel.Compiler.NodeSkeleton.Sim.Prims

/-!
# The simulation of the gadgets, the macros and the formula encoding

One `Sim2` lemma for every construction of `NodeCheck/Builder.lean`, against its transcription
in `Core.lean`; the macros are proved step by step by `sim2_tac`.
-/

namespace ZInQ.Compiler.NodeSkeleton

open Natural NodeCheck Universal

/-! ### Surjectivity of the conversions -/

mutual

/-- The inverse of `toL`. -/
def ofL : LForm → FForm
  | .eq a b => .eq a b
  | .atom f => .atom f
  | .call j => .call j
  | .and fs => .and (ofLs fs)
  | .or fs => .or (ofLs fs)

/-- The inverse of `toLs`. -/
def ofLs : List LForm → List FForm
  | [] => []
  | f :: fs => ofL f :: ofLs fs

end

mutual

theorem toL_ofL : ∀ f : LForm, toL (ofL f) = f
  | .eq _ _ => rfl
  | .atom _ => rfl
  | .call _ => rfl
  | .and fs => by simp only [ofL, toL, toLs_ofLs fs]
  | .or fs => by simp only [ofL, toL, toLs_ofLs fs]

theorem toLs_ofLs : ∀ fs : List LForm, toLs (ofLs fs) = fs
  | [] => rfl
  | f :: fs => by simp only [ofLs, toLs, toL_ofL f, toLs_ofLs fs]

end

mutual

theorem ofL_toL : ∀ f : FForm, ofL (toL f) = f
  | .eq _ _ => rfl
  | .atom _ => rfl
  | .call _ => rfl
  | .and fs => by simp only [toL, ofL, ofLs_toLs fs]
  | .or fs => by simp only [toL, ofL, ofLs_toLs fs]

theorem ofLs_toLs : ∀ fs : List FForm, ofLs (toLs fs) = fs
  | [] => rfl
  | f :: fs => by simp only [toLs, ofLs, ofL_toL f, ofLs_toLs fs]

end

theorem toL_surj : Function.Surjective toL := fun f => ⟨ofL f, toL_ofL f⟩

theorem map_surj {α β : Type} {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective (List.map f) := by
  intro l
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨l', rfl⟩ := ih
    exact ⟨a :: l', rfl⟩

section Macros

variable {Hall : List ℕ}

/-! ### Sums, products, lists -/

theorem addFrom_sim2 (acc : ℕ) (ys : List ℕ) :
    Sim2 Hall id (NodeCheck.addFrom acc ys) (addFrom acc ys) := by
  induction ys generalizing acc with
  | nil => exact Sim2.pure rfl
  | cons y ys ih => exact Sim2.bindN (nodeOp_sim2 (.inl ⟨rfl, rfl⟩)) fun i => ih i

theorem mulFrom_sim2 (acc : ℕ) (ys : List ℕ) :
    Sim2 Hall id (NodeCheck.mulFrom acc ys) (mulFrom acc ys) := by
  induction ys generalizing acc with
  | nil => exact Sim2.pure rfl
  | cons y ys ih => exact Sim2.bindN (nodeOp_sim2 (.inr ⟨rfl, rfl⟩)) fun i => ih i

theorem addL_sim2 (xs : List ℕ) : Sim2 Hall id (NodeCheck.addL xs) (addL xs) := by
  cases xs with
  | nil => exact constant_sim2 0
  | cons x xs => exact addFrom_sim2 x xs

theorem mulL_sim2 (xs : List ℕ) : Sim2 Hall id (NodeCheck.mulL xs) (mulL xs) := by
  cases xs with
  | nil => exact constant_sim2 1
  | cons x xs => exact mulFrom_sim2 x xs

theorem square_sim2 (x : ℕ) : Sim2 Hall id (NodeCheck.square x) (square x) := mulL_sim2 _

theorem scale_sim2 (n : ℤ) (x : ℕ) : Sim2 Hall id (NodeCheck.scale n x) (scale n x) :=
  Sim2.bindN (constant_sim2 n) fun _ => mulL_sim2 _

theorem seqM_sim2 {α β : Type} {er : α → β} (hs : Function.Surjective er) :
    ∀ {ms : List (FM α)} {ms' : List (HP β)}, List.Forall₂ (Sim2 Hall er) ms ms' →
      Sim2 Hall (List.map er) (NodeCheck.seqM ms) (seqM ms')
  | [], [], .nil => Sim2.pure rfl
  | _ :: _, _ :: _, .cons h hs' =>
    Sim2.bind hs h fun _ => Sim2.bind (map_surj hs) (seqM_sim2 hs hs') fun _ => Sim2.pure rfl

theorem andM_sim2 {ms : List (FM FForm)} {ms' : List (HP LForm)}
    (h : List.Forall₂ (Sim2 Hall toL) ms ms') : Sim2 Hall toL (NodeCheck.andM ms) (andM ms') :=
  Sim2.bind (map_surj toL_surj) (seqM_sim2 toL_surj h) fun fs =>
    Sim2.pure (by simp [toL, toLs_eq])

theorem power_sim2 (P Q R : ℕ) : Sim2 Hall toL (NodeCheck.power P Q R) (power P Q R) :=
  callPower_sim2 P Q R

set_option hygiene false in
/-- Proves a `Sim2` goal between a construction and its transcription, step by step. -/
macro "sim2_tac" : tactic => `(tactic| repeat' (first
  | rfl
  | (intro _)
  | (with_reducible apply Sim2.pure)
  | (with_reducible apply List.Forall₂.nil)
  | (with_reducible apply List.Forall₂.cons)
  | (with_reducible apply fresh_sim2)
  | (with_reducible apply constant_sim2)
  | (with_reducible apply addL_sim2)
  | (with_reducible apply mulL_sim2)
  | (with_reducible apply square_sim2)
  | (with_reducible apply scale_sim2)
  | (with_reducible apply power_sim2)
  | (with_reducible apply callPower_sim2)
  | (with_reducible apply andM_sim2)
  | (with_reducible apply lt_sim2)
  | (with_reducible apply odd_sim2)
  | (with_reducible apply binomial_sim2)
  | (with_reducible apply orthogonal_sim2)
  | (with_reducible apply mask_sim2)
  | (with_reducible apply bitAnd_sim2)
  | (with_reducible apply Sim2.bindN)
  | (with_reducible apply Sim2.bind toL_surj)
  | (with_reducible apply Sim2.bind (map_surj toL_surj))))

/-! ### Gadgets and macros -/

theorem lt_sim2 (a b : ℕ) : Sim2 Hall toL (NodeCheck.lt a b) (lt a b) := by
  unfold NodeCheck.lt lt
  sim2_tac

theorem odd_sim2 (x : ℕ) : Sim2 Hall toL (NodeCheck.odd x) (odd x) := by
  unfold NodeCheck.odd odd
  sim2_tac

theorem binomial_sim2 (C N K : ℕ) : Sim2 Hall toL (NodeCheck.binomial C N K) (binomial C N K) := by
  unfold NodeCheck.binomial binomial
  sim2_tac

theorem orthogonal_sim2 (a b : ℕ) :
    Sim2 Hall toL (NodeCheck.orthogonal a b) (orthogonal a b) := by
  unfold NodeCheck.orthogonal orthogonal
  sim2_tac

theorem mask_sim2 (a b : ℕ) : Sim2 Hall toL (NodeCheck.mask a b) (mask a b) := by
  unfold NodeCheck.mask mask
  sim2_tac

theorem bitAnd_sim2 (z x y : ℕ) : Sim2 Hall toL (NodeCheck.bitAnd z x y) (bitAnd z x y) := by
  unfold NodeCheck.bitAnd bitAnd
  sim2_tac

/-! ### The encoding -/

theorem forall₂_square (es : List ℕ) :
    List.Forall₂ (Sim2 Hall id) (es.map NodeCheck.square) (es.map square) := by
  induction es with
  | nil => exact .nil
  | cons e es ih => exact .cons (square_sim2 e) ih

mutual

theorem encode_sim2 : ∀ φ : FForm, Sim2 Hall id φ.encode (toL φ).encode
  | .eq _ _ => Sim2.bindN (scale_sim2 (-1) _) fun _ => addL_sim2 _
  | .atom _ => Sim2.pure rfl
  | .call _ => Sim2.pure rfl
  | .and fs => by
    show Sim2 Hall id (FForm.encode (.and fs)) (LForm.encode (.and (toLs fs)))
    unfold FForm.encode LForm.encode
    refine Sim2.bind Function.surjective_id (encodeList_sim2 fs) fun es => ?_
    refine Sim2.bind (map_surj Function.surjective_id) (seqM_sim2 Function.surjective_id
      (forall₂_square es)) fun sq => ?_
    simp only [List.map_id_fun, id_eq]
    exact addL_sim2 _
  | .or fs => by
    show Sim2 Hall id (FForm.encode (.or fs)) (LForm.encode (.or (toLs fs)))
    unfold FForm.encode LForm.encode
    exact Sim2.bind Function.surjective_id (encodeList_sim2 fs) fun _ => mulL_sim2 _

theorem encodeList_sim2 : ∀ fs : List FForm,
    Sim2 Hall id (FForm.encodeList fs) (LForm.encodeList (toLs fs))
  | [] => Sim2.pure rfl
  | f :: fs => by
    show Sim2 Hall id (FForm.encodeList (f :: fs)) (LForm.encodeList (toL f :: toLs fs))
    unfold FForm.encodeList LForm.encodeList
    exact Sim2.bind Function.surjective_id (encode_sim2 f) fun _ =>
      Sim2.bind Function.surjective_id (encodeList_sim2 fs) fun _ => Sim2.pure rfl

end

end Macros

end ZInQ.Compiler.NodeSkeleton
