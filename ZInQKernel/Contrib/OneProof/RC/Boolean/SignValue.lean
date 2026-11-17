import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lane RC1-boolean, part 1: addresses, sign characters and the sign-value expansion

Theorem 5.3 (the restricted converse, `hyp:RC`), proof of Proposition
`ex:limits-coefficient-transfer` (`diophantine_zq.tex`, lines 5647–5739; its restatement in
Appendix G is lines 10862–10931).

The final binary family is indexed by *addresses* `x ∈ 𝔽₂^b` (Definition `ex:sec7-address`,
tex 2209–2212). Its coefficient ring is the group ring `𝒪[G]` of one finite elementary abelian
two-group `G` (Definition `ex:arith-data`, tex 2743–2751), and the constituent at the address `x`
is read through the sign character `χ_x` of `G` ("sign evaluation", tex 5503, 5632, 5637–5639).
For a fixed `g ∈ G` the map `x ↦ χ_x(g)` is a character of `𝔽₂^b`, so `χ_x(g) = (-1)^{ℓ_g(x)}` for a
linear form `ℓ_g` on `𝔽₂^b`. We record exactly this datum, a family `ℓ : G → (𝔽₂^b →+ 𝔽₂)`; for
`G = 𝔽₂^b` with the standard pairing (`dotPairing`) each `χ_x` is a character of `G`
(`signChar_dotPairing_add`). An element of `R[G]` is recorded by its coefficients in the group
basis, `α : G → R`, and its sign evaluation at `x` is `α_x = Σ_g χ_x(g) α_g` (`signEval`).

Main result (kind PROVED): `signEval_expansion`, the display at tex 5666–5671: the sign-value
function of any element of `R[G]` has the form `A(x) = a_∅ + Σ_{I ≠ ∅} 2^{|I|} a_I Π_{i ∈ I} x_i`.
-/

namespace ZInQ.Manuscript.RC.Boolean

open Finset

/-- An *address* `x ∈ 𝔽₂^b` (Definition `ex:sec7-address`, tex 2209–2210). -/
abbrev Address (b : ℕ) := Fin b → ZMod 2

section SignEvaluation

variable {b : ℕ} {G : Type*}

/-- The sign value `χ_x(g) = (-1)^{ℓ_g(x)} ∈ {±1}` of the group element `g` at the address `x`, for
the family of linear forms `ℓ` attached to the sign characters of the binary group (module
docstring). -/
def signChar (ℓ : G → Address b →+ ZMod 2) (x : Address b) (g : G) : ℤ :=
  (-1) ^ (ℓ g x).val

/-- Sign evaluation `α_x = Σ_g χ_x(g) α_g` at the address `x` of the element of `R[G]` whose
group-basis coefficients are `α`. Applied to a Laurent coefficient of an element of `𝒪[G]` this is
the "sign-value function on `𝔽₂^b`" of tex 5666–5667. -/
def signEval {R : Type*} [CommRing R] [Fintype G] (ℓ : G → Address b →+ ZMod 2) (α : G → R)
    (x : Address b) : R :=
  ∑ g, (signChar ℓ x g : R) * α g

/-- Sign evaluation is additive in the element of `R[G]`. -/
theorem signEval_add {R : Type*} [CommRing R] [Fintype G] (ℓ : G → Address b →+ ZMod 2)
    (α β : G → R) (x : Address b) :
    signEval ℓ (α + β) x = signEval ℓ α x + signEval ℓ β x := by
  simp [signEval, mul_add, sum_add_distrib]

/-- Sign evaluation commutes with ring homomorphisms applied to the group-basis coefficients. -/
theorem map_signEval {R S : Type*} [CommRing R] [CommRing S] [Fintype G] (φ : R →+* S)
    (ℓ : G → Address b →+ ZMod 2) (α : G → R) (x : Address b) :
    φ (signEval ℓ α x) = signEval ℓ (fun g => φ (α g)) x := by
  simp [signEval, map_sum, map_mul, map_intCast]

/-- At the zero address every sign value is `1`, so `α_0 = Σ_g α_g` is the augmentation. -/
theorem signEval_zero {R : Type*} [CommRing R] [Fintype G] (ℓ : G → Address b →+ ZMod 2)
    (α : G → R) : signEval ℓ α 0 = ∑ g, α g := by
  simp [signEval, signChar]

/-- The standard pairing `⟨g, x⟩ = Σ_i g_i x_i` of `𝔽₂^b` with itself; with `G = 𝔽₂^b` it makes
the addresses exactly the sign characters of `G`. -/
def dotPairing (b : ℕ) (g : Address b) : Address b →+ ZMod 2 where
  toFun x := ∑ i, g i * x i
  map_zero' := by simp
  map_add' x y := by simp [mul_add, sum_add_distrib]

/-- `(-1)^{val}` turns addition in `𝔽₂` into multiplication of signs. -/
theorem neg_one_pow_val_add {R : Type*} [Monoid R] [HasDistribNeg R] (s t : ZMod 2) :
    (-1 : R) ^ (s + t).val = (-1) ^ s.val * (-1) ^ t.val := by
  have h : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have v0 : (0 : ZMod 2).val = 0 := rfl
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have v11 : ((1 : ZMod 2) + 1).val = 0 := rfl
  rcases h s with rfl | rfl <;> rcases h t with rfl | rfl
  · simp [v0]
  · simp [v0, v1]
  · simp [v0, v1]
  · rw [v11, v1]; simp

/-- For `G = 𝔽₂^b` with the standard pairing, `g ↦ χ_x(g)` is a character of `G`. -/
theorem signChar_dotPairing_add (x g h : Address b) :
    signChar (dotPairing b) x (g + h) = signChar (dotPairing b) x g * signChar (dotPairing b) x h := by
  have : (dotPairing b (g + h)) x = (dotPairing b g) x + (dotPairing b h) x := by
    simp [dotPairing, add_mul, sum_add_distrib]
  simp only [signChar, this, neg_one_pow_val_add]

/-- `(-1)^{val}` of a finite sum in `𝔽₂` is the product of the signs. -/
theorem neg_one_pow_val_sum {R : Type*} [CommMonoid R] [HasDistribNeg R] {ι : Type*}
    (s : Finset ι) (f : ι → ZMod 2) :
    (-1 : R) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1 : R) ^ (f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, neg_one_pow_val_add, ih]

/-- A linear form on `𝔽₂^b` in coordinates: `φ(x) = Σ_i x_i φ(e_i)`. -/
theorem addMonoidHom_apply_eq_sum (φ : Address b →+ ZMod 2) (x : Address b) :
    φ x = ∑ i, x i * φ (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine sum_congr rfl fun i _ => ?_
  have hx : (Pi.single i (x i) : Address b) = (x i).val • (Pi.single i 1 : Address b) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [hx, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- The sign of one coordinate: `(-1)^{val(y c)} = 1 - 2 y` if `c = 1`, and `1` if `c = 0`. -/
theorem neg_one_pow_val_mul {R : Type*} [CommRing R] (y c : ZMod 2) :
    (-1 : R) ^ (y * c).val = if c = 1 then 1 - 2 * (y.val : R) else 1 := by
  have h : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have v0 : (0 : ZMod 2).val = 0 := rfl
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases h y with rfl | rfl <;> rcases h c with rfl | rfl
  · simp [v0, h01]
  · simp [v0]
  · simp [v0, h01]
  · simp only [mul_one, v1, ite_true, pow_one, Nat.cast_one]; ring

/-- The linear-form support `J_g = {i : ℓ_g(e_i) = 1}` of the group element `g`. -/
def formSupport (ℓ : G → Address b →+ ZMod 2) (g : G) : Finset (Fin b) :=
  univ.filter fun i => ℓ g (Pi.single i 1) = 1

/-- `χ_x(g) = Π_{i ∈ J_g} (1 - 2 x_i)`, with `x_i ∈ {0, 1}`. -/
theorem signChar_eq_prod {R : Type*} [CommRing R] (ℓ : G → Address b →+ ZMod 2) (x : Address b)
    (g : G) :
    (signChar ℓ x g : R) = ∏ i ∈ formSupport ℓ g, (1 - 2 * ((x i).val : R)) := by
  have h1 : (signChar ℓ x g : R) = (-1 : R) ^ (ℓ g x).val := by
    simp [signChar]
  rw [h1, addMonoidHom_apply_eq_sum (ℓ g) x, neg_one_pow_val_sum]
  simp only [neg_one_pow_val_mul, formSupport, prod_filter]

/-- **The sign-value expansion** (tex 5666–5671; kind PROVED). The sign-value function of the
element of `R[G]` with group-basis coefficients `α` expands as
`A(x) = a_∅ + Σ_{I ≠ ∅} 2^{|I|} a_I Π_{i ∈ I} x_i` with `a_I ∈ R`. Here the term `I = ∅` of the sum
is `a_∅` (`2^0 = 1`, empty product `1`), and `x_i ∈ 𝔽₂` is read as `0` or `1` in `R`. -/
theorem signEval_expansion {R : Type*} [CommRing R] [Fintype G] (ℓ : G → Address b →+ ZMod 2)
    (α : G → R) :
    ∃ a : Finset (Fin b) → R, ∀ x : Address b,
      signEval ℓ α x = ∑ I : Finset (Fin b), 2 ^ I.card * a I * ∏ i ∈ I, ((x i).val : R) := by
  classical
  refine ⟨fun I => (-1) ^ I.card * ∑ g ∈ univ.filter (fun g => I ⊆ formSupport ℓ g), α g,
    fun x => ?_⟩
  have hpow : ∀ (J : Finset (Fin b)),
      ∏ i ∈ J, (1 - 2 * ((x i).val : R)) =
        ∑ I : Finset (Fin b), if I ⊆ J then (-2) ^ I.card * ∏ i ∈ I, ((x i).val : R) else 0 := by
    intro J
    have h1 : ∏ i ∈ J, (1 - 2 * ((x i).val : R)) = ∏ i ∈ J, (1 + (-2) * ((x i).val : R)) := by
      refine prod_congr rfl fun i _ => ?_
      ring
    have h2 : J.powerset = univ.filter (fun I => I ⊆ J) := by
      ext I; simp
    rw [h1, prod_one_add, h2, sum_filter]
    refine sum_congr rfl fun I _ => ?_
    rw [prod_mul_distrib, prod_const]
  simp only [signEval, signChar_eq_prod, hpow, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun I _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine sum_congr rfl fun g _ => ?_
  split_ifs with h
  · rw [neg_pow]
    ring
  · ring

end SignEvaluation

end ZInQ.Manuscript.RC.Boolean
