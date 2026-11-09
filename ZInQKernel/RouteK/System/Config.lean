import Mathlib

/-!
# Route K: configurations

A configuration (`docs/research/slot-k.md` §2.1) is a finite set of symbols ("primes") `x`, each with
a class `c_x ∈ {1, 3, 5, 7}` mod 8, and bits `[y/x] ∈ 𝔽₂` for `x ≠ y` satisfying reciprocity
`[x/y] + [y/x] = λ_x λ_y`, where `λ_x = [c_x ≡ 3 (mod 4)]` and `μ_x = [c_x ≡ 3, 5 (mod 8)]`.
The product class is `c(𝒞) = Π c_x mod 8`.

Here the symbols are the elements of a `Fintype` index type `ι`, classes live in `ZMod 8` and bits in
`ZMod 2`. The field `bit y x` is `[y/x]`; its diagonal values are never used (see
`ZInQ.RouteK.Config.monsky_eq_sum`).
-/

namespace ZInQ.RouteK

/-- The four odd classes mod 8. -/
def oddClasses : Finset (ZMod 8) := {1, 3, 5, 7}

/-- `λ(c) = [c ≡ 3 (mod 4)]`, for a class `c` mod 8. -/
def lam8 (c : ZMod 8) : ZMod 2 := if c = 3 ∨ c = 7 then 1 else 0

/-- `μ(c) = [c ≡ 3, 5 (mod 8)]`, for a class `c` mod 8. -/
def mu8 (c : ZMod 8) : ZMod 2 := if c = 3 ∨ c = 5 then 1 else 0

theorem oddClasses_mul {c d : ZMod 8} (hc : c ∈ oddClasses) (hd : d ∈ oddClasses) :
    c * d ∈ oddClasses := by
  revert c d; decide

theorem lam8_mul {c d : ZMod 8} (hc : c ∈ oddClasses) (hd : d ∈ oddClasses) :
    lam8 (c * d) = lam8 c + lam8 d := by
  revert c d; decide

theorem mu8_mul {c d : ZMod 8} (hc : c ∈ oddClasses) (hd : d ∈ oddClasses) :
    mu8 (c * d) = mu8 c + mu8 d := by
  revert c d; decide

@[simp] theorem lam8_one : lam8 1 = 0 := by decide
@[simp] theorem mu8_one : mu8 1 = 0 := by decide

theorem prod_mem_oddClasses {κ : Type*} (s : Finset κ) (f : κ → ZMod 8)
    (hf : ∀ k ∈ s, f k ∈ oddClasses) : ∏ k ∈ s, f k ∈ oddClasses :=
  Finset.prod_induction f (· ∈ oddClasses) (fun _ _ => oddClasses_mul) (by decide) hf

/-- `λ` is additive on products of odd classes. -/
theorem lam8_prod {κ : Type*} [DecidableEq κ] (s : Finset κ) (f : κ → ZMod 8)
    (hf : ∀ k ∈ s, f k ∈ oddClasses) : lam8 (∏ k ∈ s, f k) = ∑ k ∈ s, lam8 (f k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      lam8_mul (hf a (Finset.mem_insert_self a s))
        (prod_mem_oddClasses s f fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

/-- `μ` is additive on products of odd classes. -/
theorem mu8_prod {κ : Type*} [DecidableEq κ] (s : Finset κ) (f : κ → ZMod 8)
    (hf : ∀ k ∈ s, f k ∈ oddClasses) : mu8 (∏ k ∈ s, f k) = ∑ k ∈ s, mu8 (f k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      mu8_mul (hf a (Finset.mem_insert_self a s))
        (prod_mem_oddClasses s f fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

/-- A configuration on the index type `ι`: classes `cls x ∈ {1, 3, 5, 7}` mod 8 and symbol bits
`bit y x = [y/x]` for `x ≠ y`, subject to reciprocity `[x/y] + [y/x] = λ_x λ_y`. -/
structure Config (ι : Type*) where
  /-- The class `c_x` mod 8. -/
  cls : ι → ZMod 8
  cls_mem : ∀ x, cls x ∈ oddClasses
  /-- `bit y x = [y/x]`, the symbol of `y` at `x`. Only its off-diagonal values matter. -/
  bit : ι → ι → ZMod 2
  recip : ∀ x y, x ≠ y → bit x y + bit y x = lam8 (cls x) * lam8 (cls y)

namespace Config

variable {ι : Type*} (𝒞 : Config ι)

/-- `λ_x = [c_x ≡ 3 (mod 4)]`. -/
def lam (x : ι) : ZMod 2 := lam8 (𝒞.cls x)

/-- `μ_x = [c_x ≡ 3, 5 (mod 8)]`. -/
def mu (x : ι) : ZMod 2 := mu8 (𝒞.cls x)

/-- The product class `c(𝒞) = Π_x c_x` mod 8. -/
def prodClass [Fintype ι] : ZMod 8 := ∏ x, 𝒞.cls x

theorem prodClass_mem [Fintype ι] : 𝒞.prodClass ∈ oddClasses :=
  prod_mem_oddClasses _ _ fun x _ => 𝒞.cls_mem x

theorem recip' {x y : ι} (h : x ≠ y) : 𝒞.bit x y + 𝒞.bit y x = 𝒞.lam x * 𝒞.lam y :=
  𝒞.recip x y h

/-- For a symbol of class 1 (a glue prime), the symbols are symmetric: `[r/x] = [x/r]`. -/
theorem bit_symm_of_cls_one {r x : ι} (hr : 𝒞.cls r = 1) (h : x ≠ r) :
    𝒞.bit x r = 𝒞.bit r x := by
  have := 𝒞.recip x r h
  rw [hr, lam8_one, mul_zero] at this
  calc 𝒞.bit x r = 𝒞.bit x r + (𝒞.bit x r + 𝒞.bit r x) := by rw [this, add_zero]
    _ = 𝒞.bit r x := by ring_nf; reduce_mod_char

/-- Reindexing a configuration along an equivalence `e : κ ≃ ι`. -/
def reindex {κ : Type*} (e : κ ≃ ι) : Config κ where
  cls x := 𝒞.cls (e x)
  cls_mem x := 𝒞.cls_mem (e x)
  bit x y := 𝒞.bit (e x) (e y)
  recip x y h := 𝒞.recip (e x) (e y) (e.injective.ne h)

@[simp] theorem reindex_cls {κ : Type*} (e : κ ≃ ι) (x : κ) :
    (𝒞.reindex e).cls x = 𝒞.cls (e x) := rfl

@[simp] theorem reindex_bit {κ : Type*} (e : κ ≃ ι) (x y : κ) :
    (𝒞.reindex e).bit x y = 𝒞.bit (e x) (e y) := rfl

theorem prodClass_reindex [Fintype ι] {κ : Type*} [Fintype κ] (e : κ ≃ ι) :
    (𝒞.reindex e).prodClass = 𝒞.prodClass :=
  e.prod_comp 𝒞.cls

end Config

end ZInQ.RouteK
