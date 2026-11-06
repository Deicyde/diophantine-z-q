import ZInQKernel.Syntax.Constants.Catalogue
import ZInQKernel.Syntax.Constants.FormalMultiple

/-!
# Fixed integer expressions

Blueprint: `syntax/constants/fixed-integer-expressions.md`.

A fixed integer expression is built from integer literals, references to named constants
(of a type `R`), `add`, `mul`, `pow`, `max(e₁, …, e_k)` with `k ≥ 1`, `factorial`,
`catalogue_product`, `catalogue_max` and `least_formal_multiple`. Its value `val env e ∈ ℤ` is
defined by structural recursion, given the values `env : R → ℤ` of the named constants:

* `pow(e₁, e₂) = val(e₁)^{val(e₂)}`, a negative exponent being read as `0`;
* `max(e₁, …, e_k)` is the maximum, computed as a left fold;
* `factorial(e) = val(e)!` with `n! = 1` for `n ≤ 0`;
* the catalogue operators and the least formal multiple read their arguments through the
  natural-number truncation `Int.toNat`.

`val` is noncomputable (the catalogue and the least formal multiple are defined with
`Nat.nth` and `sInf`), and no astronomical value is ever evaluated: all later statements are
proved from the defining equations `val_literal`, `val_add`, ….
-/

namespace ZInQ.Syntax

/-- Fixed integer expressions with references to named constants of type `R`. -/
inductive FixedExpr (R : Type) where
  /-- An integer literal. -/
  | literal (z : ℤ)
  /-- A reference to an earlier named fixed constant. -/
  | ref (r : R)
  /-- `add(e₁, e₂)`. -/
  | add (a b : FixedExpr R)
  /-- `mul(e₁, e₂)`. -/
  | mul (a b : FixedExpr R)
  /-- `pow(e₁, e₂)`. -/
  | pow (a b : FixedExpr R)
  /-- `max(e₁, e₂, …, e_k)`, `k ≥ 1`: the first argument and the list of the others. -/
  | max (a : FixedExpr R) (as : List (FixedExpr R))
  /-- `factorial(e)`. -/
  | factorial (a : FixedExpr R)
  /-- `catalogue_product(e_W, e_k, e_B)`. -/
  | catalogueProduct (W k B : FixedExpr R)
  /-- `catalogue_max(e_W, e_k, e_B)`. -/
  | catalogueMax (W k B : FixedExpr R)
  /-- `least_formal_multiple(e_N)`. -/
  | leastFormalMultiple (N : FixedExpr R)

namespace FixedExpr

variable {R : Type}

mutual

/-- The value of a fixed integer expression, given the values of the named constants. -/
noncomputable def val (env : R → ℤ) : FixedExpr R → ℤ
  | literal z => z
  | ref r => env r
  | add a b => val env a + val env b
  | mul a b => val env a * val env b
  | pow a b => val env a ^ (val env b).toNat
  | max a as => valMax env (val env a) as
  | factorial a => ((val env a).toNat.factorial : ℤ)
  | catalogueProduct W k B =>
      (_root_.ZInQ.Syntax.catalogueProduct (val env W).toNat (val env k).toNat
        (val env B).toNat : ℤ)
  | catalogueMax W k B =>
      (_root_.ZInQ.Syntax.catalogueMax (val env W).toNat (val env k).toNat
        (val env B).toNat : ℤ)
  | leastFormalMultiple N =>
      (_root_.ZInQ.Syntax.leastFormalMultiple (val env N).toNat : ℤ)

/-- The running maximum `max(acc, val(e₁), …, val(e_n))` of a list of expressions. -/
noncomputable def valMax (env : R → ℤ) (acc : ℤ) : List (FixedExpr R) → ℤ
  | [] => acc
  | e :: es => valMax env (Max.max acc (val env e)) es

end

variable (env : R → ℤ)

@[simp] theorem val_literal (z : ℤ) : val env (literal z) = z := by rw [val]
@[simp] theorem val_ref (r : R) : val env (ref r) = env r := by rw [val]
@[simp] theorem val_add (a b : FixedExpr R) : val env (add a b) = val env a + val env b := by
  rw [val]
@[simp] theorem val_mul (a b : FixedExpr R) : val env (mul a b) = val env a * val env b := by
  rw [val]
@[simp] theorem val_pow (a b : FixedExpr R) :
    val env (pow a b) = val env a ^ (val env b).toNat := by rw [val]
@[simp] theorem val_factorial (a : FixedExpr R) :
    val env (factorial a) = ((val env a).toNat.factorial : ℤ) := by rw [val]
@[simp] theorem val_catalogueProduct (W k B : FixedExpr R) :
    val env (catalogueProduct W k B) =
      (_root_.ZInQ.Syntax.catalogueProduct (val env W).toNat (val env k).toNat
        (val env B).toNat : ℤ) := by rw [val]
@[simp] theorem val_catalogueMax (W k B : FixedExpr R) :
    val env (catalogueMax W k B) =
      (_root_.ZInQ.Syntax.catalogueMax (val env W).toNat (val env k).toNat
        (val env B).toNat : ℤ) := by rw [val]
@[simp] theorem val_leastFormalMultiple (N : FixedExpr R) :
    val env (leastFormalMultiple N) =
      (_root_.ZInQ.Syntax.leastFormalMultiple (val env N).toNat : ℤ) := by rw [val]

theorem valMax_eq (acc : ℤ) (es : List (FixedExpr R)) :
    valMax env acc es = (es.map (val env)).foldl Max.max acc := by
  induction es generalizing acc with
  | nil => rw [valMax]; rfl
  | cons e es ih => rw [valMax, ih]; rfl

/-- `max(e₁, …, e_k)` is the left fold of `max` over the values. -/
@[simp] theorem val_max (a : FixedExpr R) (as : List (FixedExpr R)) :
    val env (max a as) = (as.map (val env)).foldl Max.max (val env a) := by
  rw [val, valMax_eq]

theorem foldl_max_le_iff (acc n : ℤ) (l : List ℤ) :
    l.foldl Max.max acc ≤ n ↔ acc ≤ n ∧ ∀ x ∈ l, x ≤ n := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, max_le_iff, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem le_foldl_max (acc : ℤ) (l : List ℤ) :
    acc ≤ l.foldl Max.max acc ∧ ∀ x ∈ l, x ≤ l.foldl Max.max acc :=
  (foldl_max_le_iff acc _ l).1 le_rfl

/-- The value of `max(e₁, …, e_k)` is at most `n` iff every argument's value is. -/
theorem val_max_le_iff (a : FixedExpr R) (as : List (FixedExpr R)) (n : ℤ) :
    val env (max a as) ≤ n ↔ val env a ≤ n ∧ ∀ e ∈ as, val env e ≤ n := by
  simp [val_max, foldl_max_le_iff]

/-- Every argument's value is at most the value of `max(e₁, …, e_k)`. -/
theorem le_val_max (a : FixedExpr R) (as : List (FixedExpr R)) :
    val env a ≤ val env (max a as) ∧ ∀ e ∈ as, val env e ≤ val env (max a as) :=
  (val_max_le_iff env a as _).1 le_rfl

/-! ### Natural-number values

Transfer lemmas: an expression whose subexpressions have the values `(m : ℤ)`, `(n : ℤ)` of
natural numbers has the value of the corresponding natural-number formula. They let the
values of the named constants be identified with their defining formulas by rewriting alone,
without unfolding any constant. -/

section NatCast

variable {env : R → ℤ} {a b c : FixedExpr R} {m n k : ℕ}

theorem foldl_max_natCast (m : ℕ) (ns : List ℕ) :
    (ns.map (Nat.cast : ℕ → ℤ)).foldl Max.max (m : ℤ) = ((ns.foldl Max.max m : ℕ) : ℤ) := by
  induction ns generalizing m with
  | nil => rfl
  | cons n ns ih => rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← Nat.cast_max, ih]

theorem val_literal_eq {z : ℤ} (h : z = n) : val env (literal z) = n := by rw [val_literal, h]

theorem val_ref_eq {r : R} (h : env r = m) : val env (ref r) = m := by rw [val_ref, h]

theorem val_add_eq (ha : val env a = m) (hb : val env b = n) :
    val env (add a b) = ((m + n : ℕ) : ℤ) := by rw [val_add, ha, hb, Nat.cast_add]

theorem val_mul_eq (ha : val env a = m) (hb : val env b = n) :
    val env (mul a b) = ((m * n : ℕ) : ℤ) := by rw [val_mul, ha, hb, Nat.cast_mul]

theorem val_pow_eq (ha : val env a = m) (hb : val env b = n) :
    val env (pow a b) = ((m ^ n : ℕ) : ℤ) := by
  rw [val_pow, ha, hb, Int.toNat_natCast, Nat.cast_pow]

theorem val_factorial_eq (ha : val env a = m) :
    val env (factorial a) = ((m.factorial : ℕ) : ℤ) := by
  rw [val_factorial, ha, Int.toNat_natCast]

theorem val_catalogueProduct_eq (ha : val env a = m) (hb : val env b = n)
    (hc : val env c = k) :
    val env (catalogueProduct a b c) = ((_root_.ZInQ.Syntax.catalogueProduct m n k : ℕ) : ℤ) := by
  rw [val_catalogueProduct, ha, hb, hc, Int.toNat_natCast, Int.toNat_natCast, Int.toNat_natCast]

theorem val_catalogueMax_eq (ha : val env a = m) (hb : val env b = n) (hc : val env c = k) :
    val env (catalogueMax a b c) = ((_root_.ZInQ.Syntax.catalogueMax m n k : ℕ) : ℤ) := by
  rw [val_catalogueMax, ha, hb, hc, Int.toNat_natCast, Int.toNat_natCast, Int.toNat_natCast]

theorem val_leastFormalMultiple_eq (ha : val env a = m) :
    val env (leastFormalMultiple a) = ((_root_.ZInQ.Syntax.leastFormalMultiple m : ℕ) : ℤ) := by
  rw [val_leastFormalMultiple, ha, Int.toNat_natCast]

theorem val_max_eq {as : List (FixedExpr R)} {ns : List ℕ} (ha : val env a = m)
    (hs : as.map (val env) = ns.map Nat.cast) :
    val env (max a as) = ((ns.foldl Max.max m : ℕ) : ℤ) := by
  rw [val_max, hs, ha, foldl_max_natCast]

theorem val_max_two_eq {a₁ a₂ : FixedExpr R} {n₁ n₂ : ℕ} (ha : val env a = m)
    (h₁ : val env a₁ = n₁) (h₂ : val env a₂ = n₂) :
    val env (max a [a₁, a₂]) = ((Max.max (Max.max m n₁) n₂ : ℕ) : ℤ) := by
  rw [val_max_eq (ns := [n₁, n₂]) ha
    (by rw [List.map_cons, List.map_cons, List.map_nil, h₁, h₂]; rfl)]
  rfl

theorem val_max_three_eq {a₁ a₂ a₃ : FixedExpr R} {n₁ n₂ n₃ : ℕ} (ha : val env a = m)
    (h₁ : val env a₁ = n₁) (h₂ : val env a₂ = n₂) (h₃ : val env a₃ = n₃) :
    val env (max a [a₁, a₂, a₃]) = ((Max.max (Max.max (Max.max m n₁) n₂) n₃ : ℕ) : ℤ) := by
  rw [val_max_eq (ns := [n₁, n₂, n₃]) ha
    (by rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, h₁, h₂, h₃]; rfl)]
  rfl

end NatCast

/-! ### References -/

mutual

/-- The named constants referenced by an expression. -/
def refs : FixedExpr R → List R
  | literal _ => []
  | ref r => [r]
  | add a b => refs a ++ refs b
  | mul a b => refs a ++ refs b
  | pow a b => refs a ++ refs b
  | max a as => refs a ++ refsList as
  | factorial a => refs a
  | catalogueProduct W k B => refs W ++ refs k ++ refs B
  | catalogueMax W k B => refs W ++ refs k ++ refs B
  | leastFormalMultiple N => refs N

/-- The named constants referenced by a list of expressions. -/
def refsList : List (FixedExpr R) → List R
  | [] => []
  | e :: es => refs e ++ refsList es

end

@[simp] theorem refs_literal (z : ℤ) : refs (literal z : FixedExpr R) = [] := by rw [refs]
@[simp] theorem refs_ref (r : R) : refs (ref r) = [r] := by rw [refs]

variable {env} {env' : R → ℤ}

mutual

/-- The value of an expression depends only on the values of the constants it references. -/
theorem val_congr : ∀ e : FixedExpr R, (∀ r ∈ refs e, env r = env' r) → val env e = val env' e
  | literal z, _ => by simp
  | ref r, h => by simpa using h r (by simp)
  | add a b, h => by
      rw [refs] at h
      simp only [val_add, val_congr a fun r hr => h r (List.mem_append_left _ hr),
        val_congr b fun r hr => h r (List.mem_append_right _ hr)]
  | mul a b, h => by
      rw [refs] at h
      simp only [val_mul, val_congr a fun r hr => h r (List.mem_append_left _ hr),
        val_congr b fun r hr => h r (List.mem_append_right _ hr)]
  | pow a b, h => by
      rw [refs] at h
      simp only [val_pow, val_congr a fun r hr => h r (List.mem_append_left _ hr),
        val_congr b fun r hr => h r (List.mem_append_right _ hr)]
  | max a as, h => by
      rw [refs] at h
      rw [val, val, val_congr a fun r hr => h r (List.mem_append_left _ hr),
        valMax_congr _ as fun r hr => h r (List.mem_append_right _ hr)]
  | factorial a, h => by
      rw [refs] at h
      simp only [val_factorial, val_congr a h]
  | catalogueProduct W k B, h => by
      rw [refs] at h
      simp only [List.mem_append] at h
      simp only [val_catalogueProduct, val_congr W fun r hr => h r (.inl (.inl hr)),
        val_congr k fun r hr => h r (.inl (.inr hr)), val_congr B fun r hr => h r (.inr hr)]
  | catalogueMax W k B, h => by
      rw [refs] at h
      simp only [List.mem_append] at h
      simp only [val_catalogueMax, val_congr W fun r hr => h r (.inl (.inl hr)),
        val_congr k fun r hr => h r (.inl (.inr hr)), val_congr B fun r hr => h r (.inr hr)]
  | leastFormalMultiple N, h => by
      rw [refs] at h
      simp only [val_leastFormalMultiple, val_congr N h]

theorem valMax_congr : ∀ (acc : ℤ) (es : List (FixedExpr R)),
    (∀ r ∈ refsList es, env r = env' r) → valMax env acc es = valMax env' acc es
  | acc, [], _ => by rw [valMax, valMax]
  | acc, e :: es, h => by
      rw [refsList] at h
      rw [valMax, valMax, val_congr e fun r hr => h r (List.mem_append_left _ hr),
        valMax_congr _ es fun r hr => h r (List.mem_append_right _ hr)]

end

end FixedExpr

/- Values of fixed expressions are only ever computed through the equations above: from here
on the elaborator may not unfold `val` (a failed unification would otherwise start evaluating
astronomical constants). -/
attribute [irreducible] FixedExpr.val FixedExpr.valMax

end ZInQ.Syntax
