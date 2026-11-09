import ZInQKernel.Compiler.Circuits.Construction

/-!
# Compilation and private witnesses over the naturals

1. For every formula `φ` and `x : ℕ → ℕ`, `κ(φ)(x) = 0` iff `φ` holds naturally at `x`
   (`compile_zv_eq_zero_iff`).
2. A natural construction run from counter `c₀` to `c₁` with argument polynomials in variables
   of a set `U` below `c₀` produces a formula whose variables lie in `U ∪ [c₀, c₁)`. The
   statement `∃ y : [c₀, c₁) → ℕ, φ holds naturally at x[y]` depends only on `x` outside
   `[c₀, c₁)` (`exists_agree_congr`); for a conjunction of formulas produced on consecutive
   subintervals it is the conjunction of the statements of the conjuncts (`Spec.and`), for a
   disjunction their disjunction (`Spec.or`), and a fresh variable becomes an existential
   quantifier (`Spec.fresh`).
3. A power call whose block is private may be replaced by the statement that some natural
   values of its block make the template vanish (`callPower_spec`).

`Spec φ U c₀ c₁ R` packages the hypotheses and the conclusion of item 2 for one formula:
`c₀ ≤ c₁`, the variables of `κ(φ)` lie in `U ∪ [c₀, c₁)`, and the private-witness statement is
equivalent to `R x` for every `x`. `MSpec τ m U R` says that a construction `m` satisfies it at
every state whose counter lies above `U`.

(Blueprint: `compiler/natural/formulas/natural-compilation.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-! ### Values at natural points -/

/-- The integer value of a polynomial at a natural point. -/
def zv (x : ℕ → ℕ) (f : Poly) : ℤ := MvPolynomial.eval (fun i => (x i : ℤ)) f

/-- A natural point as a rational assignment. -/
def qa (x : ℕ → ℕ) : ℕ → ℚ := fun i => (x i : ℚ)

theorem ev_qa (x : ℕ → ℕ) (f : Poly) : ev (qa x) f = (zv x f : ℚ) := by
  show eval₂ (Int.castRingHom ℚ) (qa x) f =
    (Int.castRingHom ℚ) (eval₂ (RingHom.id ℤ) (fun i => (x i : ℤ)) f)
  rw [eval₂_comp_left, RingHom.comp_id]
  congr 1

@[simp] theorem zv_X (x : ℕ → ℕ) (i : ℕ) : zv x (X i) = x i := by simp [zv]

@[simp] theorem zv_C (x : ℕ → ℕ) (c : ℤ) : zv x (C c) = c := by simp [zv]

@[simp] theorem zv_add (x : ℕ → ℕ) (f g : Poly) : zv x (f + g) = zv x f + zv x g := by
  simp [zv]

@[simp] theorem zv_mul (x : ℕ → ℕ) (f g : Poly) : zv x (f * g) = zv x f * zv x g := by
  simp [zv]

@[simp] theorem zv_sub (x : ℕ → ℕ) (f g : Poly) : zv x (f - g) = zv x f - zv x g := by
  simp [zv]

@[simp] theorem zv_pow (x : ℕ → ℕ) (f : Poly) (n : ℕ) : zv x (f ^ n) = zv x f ^ n := by
  simp [zv]

@[simp] theorem zv_zero (x : ℕ → ℕ) : zv x 0 = 0 := by simp [zv]

@[simp] theorem zv_one (x : ℕ → ℕ) : zv x 1 = 1 := by simp [zv]

@[simp] theorem zv_natCast (x : ℕ → ℕ) (n : ℕ) : zv x (n : Poly) = n := by simp [zv]

@[simp] theorem zv_intCast (x : ℕ → ℕ) (n : ℤ) : zv x (n : Poly) = n := by simp [zv]

@[simp] theorem zv_ofNat (x : ℕ → ℕ) (n : ℕ) [n.AtLeastTwo] :
    zv x (no_index (OfNat.ofNat n : Poly)) = OfNat.ofNat n := by simp [zv]

theorem zv_list_sum (x : ℕ → ℕ) (l : List Poly) : zv x l.sum = (l.map (zv x)).sum := by
  unfold zv; rw [map_list_sum]

theorem zv_list_prod (x : ℕ → ℕ) (l : List Poly) : zv x l.prod = (l.map (zv x)).prod := by
  unfold zv; rw [map_list_prod]

/-- The value depends only on the variables of the polynomial. -/
theorem zv_congr {x y : ℕ → ℕ} {f : Poly} (h : ∀ i ∈ f.vars, x i = y i) : zv x f = zv y f := by
  have := ev_congr (x := qa x) (y := qa y) (f := f) fun i hi => by simp [qa, h i hi]
  rw [ev_qa, ev_qa] at this
  exact_mod_cast this

/-- The natural value of a polynomial at a natural point (the truncation of `zv`). -/
def nv (x : ℕ → ℕ) (f : Poly) : ℕ := (zv x f).toNat

/-- `f` takes natural values at natural points (true when its coefficients are natural). -/
def IsNat (f : Poly) : Prop := ∀ x, 0 ≤ zv x f

theorem IsNat.zv_eq {f : Poly} (hf : IsNat f) (x : ℕ → ℕ) : zv x f = nv x f := by
  rw [nv, Int.toNat_of_nonneg (hf x)]

theorem IsNat.X (i : ℕ) : IsNat (X i) := fun x => by simp

theorem IsNat.natCast (n : ℕ) : IsNat (C (n : ℤ)) := fun x => by simp

theorem IsNat.ofNat (n : ℕ) [n.AtLeastTwo] : IsNat (C (OfNat.ofNat n : ℤ)) := IsNat.natCast n

theorem IsNat.zero : IsNat (C 0) := fun x => by simp

theorem IsNat.one : IsNat (C 1) := fun x => by simp

theorem IsNat.add {f g : Poly} (hf : IsNat f) (hg : IsNat g) : IsNat (f + g) := fun x => by
  simpa using add_nonneg (hf x) (hg x)

theorem IsNat.mul {f g : Poly} (hf : IsNat f) (hg : IsNat g) : IsNat (f * g) := fun x => by
  simpa using mul_nonneg (hf x) (hg x)

theorem IsNat.list_sum {l : List Poly} (h : ∀ f ∈ l, IsNat f) : IsNat l.sum := by
  induction l with
  | nil => exact fun x => by simp
  | cons f l ih =>
    rw [List.sum_cons]
    exact (h f List.mem_cons_self).add (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem IsNat.list_prod {l : List Poly} (h : ∀ f ∈ l, IsNat f) : IsNat l.prod := by
  induction l with
  | nil => exact fun x => by simp
  | cons f l ih =>
    rw [List.prod_cons]
    exact (h f List.mem_cons_self).mul (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem nv_X (x : ℕ → ℕ) (i : ℕ) : nv x (X i) = x i := by simp [nv]

theorem nv_C (x : ℕ → ℕ) (n : ℕ) : nv x (C (n : ℤ)) = n := by simp [nv]

theorem nv_add {f g : Poly} (hf : IsNat f) (hg : IsNat g) (x : ℕ → ℕ) :
    nv x (f + g) = nv x f + nv x g := by
  have := (hf.add hg).zv_eq x
  rw [zv_add, hf.zv_eq, hg.zv_eq] at this
  exact_mod_cast this.symm

theorem nv_mul {f g : Poly} (hf : IsNat f) (hg : IsNat g) (x : ℕ → ℕ) :
    nv x (f * g) = nv x f * nv x g := by
  have := (hf.mul hg).zv_eq x
  rw [zv_mul, hf.zv_eq, hg.zv_eq] at this
  exact_mod_cast this.symm

theorem nv_congr {x y : ℕ → ℕ} {f : Poly} (h : ∀ i ∈ f.vars, x i = y i) : nv x f = nv y f := by
  rw [nv, nv, zv_congr h]

/-! ### Holding naturally -/

/-- A formula holds naturally at `x : ℕ → ℕ` when it holds at the integer point `(x_i)_i`. -/
def NHolds (x : ℕ → ℕ) (φ : Formula) : Prop := φ.Holds (qa x)

@[simp] theorem nholds_eq (x : ℕ → ℕ) (a b : Poly) :
    NHolds x (.eq a b) ↔ zv x a = zv x b := by
  simp [NHolds, ev_qa]

@[simp] theorem nholds_atom (x : ℕ → ℕ) (f : Poly) : NHolds x (.atom f) ↔ zv x f = 0 := by
  simp [NHolds, ev_qa]

@[simp] theorem nholds_call (x : ℕ → ℕ) (τ : ExPoly) (g : Fin τ.params → Poly) (w : ℕ) :
    NHolds x (.call τ g w) ↔ zv x (τ.call g w) = 0 := by
  simp [NHolds, ev_qa]

@[simp] theorem nholds_and (x : ℕ → ℕ) (fs : List Formula) :
    NHolds x (.and fs) ↔ ∀ φ ∈ fs, NHolds x φ := by
  simp [NHolds]

@[simp] theorem nholds_or (x : ℕ → ℕ) (fs : List Formula) :
    NHolds x (.or fs) ↔ ∃ φ ∈ fs, NHolds x φ := by
  simp [NHolds]

/-- **Compilation over the naturals** (item 1). For every formula `φ` and every
`x : ℕ → ℕ`, `κ(φ)(x) = 0` iff `φ` holds naturally at `x`. -/
theorem compile_zv_eq_zero_iff (φ : Formula) (x : ℕ → ℕ) : zv x φ.compile = 0 ↔ NHolds x φ := by
  rw [NHolds, ← Formula.ev_compile_eq_zero_iff, ev_qa]
  exact_mod_cast Iff.rfl

theorem nholds_congr {φ : Formula} {x y : ℕ → ℕ} (h : ∀ i ∈ φ.compile.vars, x i = y i) :
    NHolds x φ ↔ NHolds y φ := by
  rw [← compile_zv_eq_zero_iff, ← compile_zv_eq_zero_iff, zv_congr h]

/-! ### Private witness intervals -/

/-- `y` agrees with `x` outside the interval `[c₀, c₁)`: `y = x[y|_{[c₀,c₁)}]`. -/
def Agree (x y : ℕ → ℕ) (c₀ c₁ : ℕ) : Prop := ∀ i, ¬ (c₀ ≤ i ∧ i < c₁) → y i = x i

theorem Agree.refl (x : ℕ → ℕ) (c₀ c₁ : ℕ) : Agree x x c₀ c₁ := fun _ _ => rfl

theorem Agree.mono {x y : ℕ → ℕ} {c₀ c₁ d₀ d₁ : ℕ} (h : Agree x y c₀ c₁) (h₀ : d₀ ≤ c₀)
    (h₁ : c₁ ≤ d₁) : Agree x y d₀ d₁ := fun i hi => h i fun hc => hi ⟨by omega, by omega⟩

/-- The override `x[y|_{[c₀,c₁)}]`. -/
def override (x y : ℕ → ℕ) (c₀ c₁ : ℕ) (i : ℕ) : ℕ := if c₀ ≤ i ∧ i < c₁ then y i else x i

theorem agree_override (x y : ℕ → ℕ) (c₀ c₁ : ℕ) : Agree x (override x y c₀ c₁) c₀ c₁ :=
  fun i hi => by simp [override, hi]

/-- Variables of `κ(φ)` lie in `U ∪ [c₀, c₁)`. -/
def Local (φ : Formula) (U : Set ℕ) (c₀ c₁ : ℕ) : Prop :=
  VarsIn φ.compile fun i => i ∈ U ∨ (c₀ ≤ i ∧ i < c₁)

/-- **Item 2, first part.** If the variables of `κ(φ)` lie below `c₁`, the private-witness
statement over `[c₀, c₁)` depends only on `x` below `c₀`. -/
theorem exists_agree_congr {φ : Formula} {c₀ c₁ : ℕ} (hφ : VarsLT φ.compile c₁) {x x' : ℕ → ℕ}
    (h : ∀ i < c₀, x i = x' i) :
    (∃ y, Agree x y c₀ c₁ ∧ NHolds y φ) ↔ (∃ y, Agree x' y c₀ c₁ ∧ NHolds y φ) := by
  have key : ∀ x x' : ℕ → ℕ, (∀ i < c₀, x i = x' i) →
      (∃ y, Agree x y c₀ c₁ ∧ NHolds y φ) → (∃ y, Agree x' y c₀ c₁ ∧ NHolds y φ) := by
    rintro x x' h ⟨y, hy, hφy⟩
    refine ⟨override x' y c₀ c₁, agree_override _ _ _ _, (nholds_congr fun i hi => ?_).1 hφy⟩
    have := hφ i hi
    unfold override
    split_ifs with hc
    · rfl
    · rw [hy i hc]; exact h i (by omega)
  exact ⟨key x x' h, key x' x fun i hi => (h i hi).symm⟩

/-- The hypotheses and conclusion of item 2 for one formula produced on `[c₀, c₁)`. -/
structure Spec (φ : Formula) (U : Set ℕ) (c₀ c₁ : ℕ) (R : (ℕ → ℕ) → Prop) : Prop where
  le : c₀ ≤ c₁
  loc : Local φ U c₀ c₁
  sem : ∀ x, (∃ y, Agree x y c₀ c₁ ∧ NHolds y φ) ↔ R x

theorem Spec.congr {φ : Formula} {U : Set ℕ} {c₀ c₁ : ℕ} {R R' : (ℕ → ℕ) → Prop}
    (h : Spec φ U c₀ c₁ R) (hR : ∀ x, R x ↔ R' x) : Spec φ U c₀ c₁ R' :=
  ⟨h.le, h.loc, fun x => (h.sem x).trans (hR x)⟩

/-- The list version: the formulas `φs`, all local, hold together. -/
structure SpecL (φs : List Formula) (U : Set ℕ) (c₀ c₁ : ℕ) (R : (ℕ → ℕ) → Prop) : Prop where
  le : c₀ ≤ c₁
  loc : ∀ φ ∈ φs, Local φ U c₀ c₁
  sem : ∀ x, (∃ y, Agree x y c₀ c₁ ∧ ∀ φ ∈ φs, NHolds y φ) ↔ R x

/-- Restricting a witness assignment to the interval of one formula. -/
theorem nholds_override_iff {φ : Formula} {U : Set ℕ} {c₀ c₁ : ℕ} (hloc : Local φ U c₀ c₁)
    {x y : ℕ → ℕ} (hxy : ∀ i ∈ U, y i = x i) :
    NHolds (override x y c₀ c₁) φ ↔ NHolds y φ := by
  refine nholds_congr fun i hi => ?_
  unfold override
  rcases hloc i hi with h | h
  · split_ifs
    · rfl
    · exact (hxy i h).symm
  · simp [h]

theorem SpecL.nil (U : Set ℕ) (c : ℕ) : SpecL [] U c c fun _ => True :=
  ⟨le_rfl, by simp, fun x => by simpa using ⟨x, Agree.refl x c c⟩⟩

/-- **Conjunction** (item 2): a formula produced on `[c₀, c₁)` followed by formulas produced on
`[c₁, c₂)`. -/
theorem SpecL.cons {φ : Formula} {φs : List Formula} {U : Set ℕ} {c₀ c₁ c₂ : ℕ}
    {R Rs : (ℕ → ℕ) → Prop} (h : Spec φ U c₀ c₁ R) (hs : SpecL φs U c₁ c₂ Rs)
    (hU : ∀ i ∈ U, i < c₀) : SpecL (φ :: φs) U c₀ c₂ fun x => R x ∧ Rs x := by
  have h01 := h.le
  have h12 := hs.le
  refine ⟨h01.trans h12, ?_, fun x => ?_⟩
  · intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact h.loc.mono fun i hi => hi.imp_right fun hi => ⟨hi.1, by omega⟩
    · exact (hs.loc ψ hψ).mono fun i hi => hi.imp_right fun hi => ⟨by omega, hi.2⟩
  constructor
  · rintro ⟨y, hy, hall⟩
    have hyU : ∀ i ∈ U, y i = x i := fun i hi => hy i fun hc => by have := hU i hi; omega
    refine ⟨(h.sem x).1 ⟨override x y c₀ c₁, agree_override _ _ _ _, ?_⟩,
      (hs.sem x).1 ⟨override x y c₁ c₂, agree_override _ _ _ _, fun ψ hψ => ?_⟩⟩
    · exact (nholds_override_iff h.loc hyU).2 (hall φ List.mem_cons_self)
    · exact (nholds_override_iff (hs.loc ψ hψ) hyU).2 (hall ψ (List.mem_cons_of_mem _ hψ))
  · rintro ⟨hR, hRs⟩
    obtain ⟨y₁, hy₁, hφ⟩ := (h.sem x).2 hR
    obtain ⟨y₂, hy₂, hφs⟩ := (hs.sem x).2 hRs
    let y : ℕ → ℕ := fun i => if i < c₁ then y₁ i else y₂ i
    refine ⟨y, fun i hi => ?_, ?_⟩
    · simp only [y]
      split_ifs with hc
      · exact hy₁ i fun hc' => hi ⟨hc'.1, by omega⟩
      · exact hy₂ i fun hc' => hi ⟨by omega, hc'.2⟩
    · intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · refine (nholds_congr fun i hi => ?_).2 hφ
        simp only [y]
        rcases h.loc i hi with hi | hi
        · have := hU i hi
          rw [ite_eq_left (show i < c₁ by omega)]
        · rw [ite_eq_left hi.2]
      · refine (nholds_congr fun i hi => ?_).2 (hφs ψ hψ)
        simp only [y]
        split_ifs with hc
        · rcases hs.loc ψ hψ i hi with hi | hi
          · have := hU i hi
            rw [hy₁ i (by omega), hy₂ i (by omega)]
          · omega
        · rfl

theorem local_and {φs : List Formula} {U : Set ℕ} {c₀ c₁ : ℕ} (h : ∀ φ ∈ φs, Local φ U c₀ c₁) :
    Local (.and φs) U c₀ c₁ := by
  unfold Local
  rw [Formula.compile_and]
  refine VarsIn.list_sum fun f hf => ?_
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
  exact (h φ hφ).pow 2

theorem local_or {φs : List Formula} {U : Set ℕ} {c₀ c₁ : ℕ} (h : ∀ φ ∈ φs, Local φ U c₀ c₁) :
    Local (.or φs) U c₀ c₁ := by
  unfold Local
  rw [Formula.compile_or]
  refine VarsIn.list_prod fun f hf => ?_
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
  exact h φ hφ

theorem SpecL.and {φs : List Formula} {U : Set ℕ} {c₀ c₁ : ℕ} {R : (ℕ → ℕ) → Prop}
    (h : SpecL φs U c₀ c₁ R) : Spec (.and φs) U c₀ c₁ R :=
  ⟨h.le, local_and h.loc, fun x => by simpa using h.sem x⟩

/-- The disjunctive list version. -/
structure SpecO (φs : List Formula) (U : Set ℕ) (c₀ c₁ : ℕ) (R : (ℕ → ℕ) → Prop) : Prop where
  le : c₀ ≤ c₁
  loc : ∀ φ ∈ φs, Local φ U c₀ c₁
  sem : ∀ x, (∃ y, Agree x y c₀ c₁ ∧ ∃ φ ∈ φs, NHolds y φ) ↔ R x

theorem SpecO.nil (U : Set ℕ) (c : ℕ) : SpecO [] U c c fun _ => False :=
  ⟨le_rfl, by simp, fun x => by simp⟩

/-- **Disjunction** (item 2): the variables of the inactive disjuncts may take any value. -/
theorem SpecO.cons {φ : Formula} {φs : List Formula} {U : Set ℕ} {c₀ c₁ c₂ : ℕ}
    {R Rs : (ℕ → ℕ) → Prop} (h : Spec φ U c₀ c₁ R) (hs : SpecO φs U c₁ c₂ Rs)
    (hU : ∀ i ∈ U, i < c₀) : SpecO (φ :: φs) U c₀ c₂ fun x => R x ∨ Rs x := by
  have h01 := h.le
  have h12 := hs.le
  refine ⟨h01.trans h12, ?_, fun x => ?_⟩
  · intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact h.loc.mono fun i hi => hi.imp_right fun hi => ⟨hi.1, by omega⟩
    · exact (hs.loc ψ hψ).mono fun i hi => hi.imp_right fun hi => ⟨by omega, hi.2⟩
  constructor
  · rintro ⟨y, hy, ψ, hψ, hψy⟩
    have hyU : ∀ i ∈ U, y i = x i := fun i hi => hy i fun hc => by have := hU i hi; omega
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact Or.inl ((h.sem x).1 ⟨_, agree_override _ _ _ _, (nholds_override_iff h.loc hyU).2 hψy⟩)
    · exact Or.inr ((hs.sem x).1 ⟨_, agree_override _ _ _ _, ψ, hψ,
        (nholds_override_iff (hs.loc ψ hψ) hyU).2 hψy⟩)
  · rintro (hR | hRs)
    · obtain ⟨y, hy, hφ⟩ := (h.sem x).2 hR
      exact ⟨y, hy.mono le_rfl h12, φ, List.mem_cons_self, hφ⟩
    · obtain ⟨y, hy, ψ, hψ, hψy⟩ := (hs.sem x).2 hRs
      exact ⟨y, hy.mono h01 le_rfl, ψ, List.mem_cons_of_mem _ hψ, hψy⟩

theorem SpecO.or {φs : List Formula} {U : Set ℕ} {c₀ c₁ : ℕ} {R : (ℕ → ℕ) → Prop}
    (h : SpecO φs U c₀ c₁ R) : Spec (.or φs) U c₀ c₁ R :=
  ⟨h.le, local_or h.loc, fun x => by simpa using h.sem x⟩

/-- **Fresh variables** (item 2): a fresh variable `X_c` followed by a construction on
`[c + 1, c₁)` that may use it. -/
theorem Spec.fresh {φ : Formula} {U : Set ℕ} {c c₁ : ℕ} {R : (ℕ → ℕ) → Prop}
    (h : Spec φ (insert c U) (c + 1) c₁ R) :
    Spec φ U c c₁ fun x => ∃ z, R (Function.update x c z) := by
  refine ⟨by have := h.le; omega, h.loc.mono fun i hi => ?_, fun x => ?_⟩
  · rcases hi with hi | hi
    · rcases Set.mem_insert_iff.1 hi with rfl | hi
      · exact Or.inr ⟨le_rfl, by have := h.le; omega⟩
      · exact Or.inl hi
    · exact Or.inr ⟨by omega, hi.2⟩
  constructor
  · rintro ⟨y, hy, hφ⟩
    refine ⟨y c, (h.sem _).1 ⟨y, fun i hi => ?_, hφ⟩⟩
    by_cases hic : i = c
    · subst hic; simp
    · rw [Function.update_of_ne hic]
      exact hy i fun hc => hi ⟨by omega, hc.2⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy, hφ⟩ := (h.sem _).2 hz
    refine ⟨y, fun i hi => ?_, hφ⟩
    have hc1 := h.le
    have hic : i ≠ c := by rintro rfl; exact hi ⟨le_rfl, by omega⟩
    rw [hy i fun hc => hi ⟨by omega, hc.2⟩, Function.update_of_ne hic]

/-! ### Constructions -/

/-- A construction `m` satisfies `Spec` with relation `R` at every state whose counter lies
above the allowed variables `U`. -/
def MSpec (τ : ExPoly) (m : NM NForm) (U : Set ℕ) (R : (ℕ → ℕ) → Prop) : Prop :=
  ∀ s : State, (∀ i ∈ U, i < s.next) → Spec ((m s).1.toFormula τ) U s.next (m s).2.next R

theorem MSpec.congr {τ : ExPoly} {m : NM NForm} {U : Set ℕ} {R R' : (ℕ → ℕ) → Prop}
    (h : MSpec τ m U R) (hR : ∀ x, R x ↔ R' x) : MSpec τ m U R' :=
  fun s hs => (h s hs).congr hR

/-- An expression construction returns an expression with polynomial `P` and changes neither
the counter, nor the explicit variables, nor the blocks; it only extends the node list. -/
def IsExpr (m : NM Ex) (P : Poly) : Prop :=
  ∀ s, (m s).1.poly = P ∧ (m s).2.next = s.next ∧ (m s).2.vars = s.vars ∧
    (m s).2.blocks = s.blocks ∧ s.nodes <+: (m s).2.nodes

theorem node_spec (n : NatNode) (s : State) :
    (node n s).2.next = s.next ∧ (node n s).2.vars = s.vars ∧ (node n s).2.blocks = s.blocks ∧
      s.nodes <+: (node n s).2.nodes := by
  unfold node
  split
  · exact ⟨rfl, rfl, rfl, List.prefix_refl _⟩
  · exact ⟨rfl, rfl, rfl, List.prefix_append _ _⟩

theorem IsExpr.pure (h : Ex) : IsExpr (Pure.pure h) h.poly :=
  fun s => ⟨rfl, rfl, rfl, rfl, List.prefix_refl _⟩

theorem IsExpr.bind {m : NM Ex} {P Q : Poly} {f : Ex → NM Ex} (hm : IsExpr m P)
    (hf : ∀ h : Ex, h.poly = P → IsExpr (f h) Q) : IsExpr (m >>= f) Q := fun s => by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm s
  obtain ⟨k1, k2, k3, k4, k5⟩ := hf (m s).1 h1 (m s).2
  exact ⟨k1, k2.trans h2, k3.trans h3, k4.trans h4, h5.trans k5⟩

theorem IsExpr.constant (c : ℤ) : IsExpr (constant c) (C c) := fun s => by
  obtain ⟨h1, h2, h3, h4⟩ := node_spec (.const c) s
  exact ⟨rfl, h1, h2, h3, h4⟩

theorem IsExpr.addFrom (acc : Ex) (l : List Ex) :
    IsExpr (addFrom acc l) (acc.poly + (l.map Ex.poly).sum) := by
  induction l generalizing acc with
  | nil => simpa [Natural.addFrom] using IsExpr.pure acc
  | cons y ys ih =>
    intro s
    obtain ⟨h1, h2, h3, h4⟩ := node_spec (.add acc.node y.node) s
    obtain ⟨k1, k2, k3, k4, k5⟩ := ih ⟨(node (.add acc.node y.node) s).1, acc.poly + y.poly⟩
      (node (.add acc.node y.node) s).2
    refine ⟨?_, k2.trans h1, k3.trans h2, k4.trans h3, h4.trans k5⟩
    simp only [Natural.addFrom, NM.bind_apply] at k1 ⊢
    rw [k1]
    simp [add_assoc]

theorem IsExpr.mulFrom (acc : Ex) (l : List Ex) :
    IsExpr (mulFrom acc l) (acc.poly * (l.map Ex.poly).prod) := by
  induction l generalizing acc with
  | nil => simpa [Natural.mulFrom] using IsExpr.pure acc
  | cons y ys ih =>
    intro s
    obtain ⟨h1, h2, h3, h4⟩ := node_spec (.mul acc.node y.node) s
    obtain ⟨k1, k2, k3, k4, k5⟩ := ih ⟨(node (.mul acc.node y.node) s).1, acc.poly * y.poly⟩
      (node (.mul acc.node y.node) s).2
    refine ⟨?_, k2.trans h1, k3.trans h2, k4.trans h3, h4.trans k5⟩
    simp only [Natural.mulFrom, NM.bind_apply] at k1 ⊢
    rw [k1]
    simp [mul_assoc]

theorem IsExpr.addL (l : List Ex) : IsExpr (addL l) (l.map Ex.poly).sum := by
  cases l with
  | nil => simpa [Natural.addL] using IsExpr.constant 0
  | cons x xs => simpa [Natural.addL] using IsExpr.addFrom x xs

theorem IsExpr.mulL (l : List Ex) : IsExpr (mulL l) (l.map Ex.poly).prod := by
  cases l with
  | nil => simpa [Natural.mulL] using IsExpr.constant 1
  | cons x xs => simpa [Natural.mulL] using IsExpr.mulFrom x xs

theorem IsExpr.square (x : Ex) : IsExpr (square x) (x.poly * x.poly) := by
  simpa [Natural.square] using IsExpr.mulL [x, x]

theorem IsExpr.scale (n : ℤ) (x : Ex) : IsExpr (scale n x) (C n * x.poly) := by
  unfold Natural.scale
  exact (IsExpr.constant n).bind fun h hh => by simpa [hh] using IsExpr.mulL [h, x]

/-- Expression constructions before a formula do not change its specification. -/
theorem MSpec.expr_bind {τ : ExPoly} {m : NM Ex} {P : Poly} {f : Ex → NM NForm} {U : Set ℕ}
    {R : (ℕ → ℕ) → Prop} (hm : IsExpr m P) (hf : ∀ h : Ex, h.poly = P → MSpec τ (f h) U R) :
    MSpec τ (m >>= f) U R := fun s hs => by
  obtain ⟨h1, h2, -⟩ := hm s
  have := hf (m s).1 h1 (m s).2 (by rw [h2]; exact hs)
  simpa [h2] using this

/-- An atom `a ≐ b`: no witnesses. -/
theorem MSpec.eq (τ : ExPoly) {a b : Ex} {U : Set ℕ} (ha : VarsIn a.poly (· ∈ U))
    (hb : VarsIn b.poly (· ∈ U)) :
    MSpec τ (Pure.pure (.eq a b)) U fun x => zv x a.poly = zv x b.poly := fun _ _ => by
  refine ⟨le_rfl, ?_, fun x => ?_⟩
  · simp only [NM.pure_apply, NForm.toFormula, Local, Formula.compile_eq]
    exact (ha.sub hb).mono fun i hi => Or.inl hi
  · simp only [NM.pure_apply, NForm.toFormula, nholds_eq]
    constructor
    · rintro ⟨y, hy, h⟩
      rwa [show y = x from funext fun i => hy i (by omega)] at h
    · exact fun h => ⟨x, Agree.refl _ _ _, h⟩

theorem fresh_apply_next (s : State) : (fresh s).2.next = s.next + 1 := by
  simp only [fresh]
  rw [(node_spec _ _).1]

theorem fresh_apply_poly (s : State) : (fresh s).1.poly = X s.next := rfl

/-- **Fresh variables**, construction form. -/
theorem MSpec.fresh_bind {τ : ExPoly} {f : Ex → NM NForm} {U : Set ℕ} {s : State}
    {R : (ℕ → ℕ) → Prop}
    (h : Spec ((f (fresh s).1 (fresh s).2).1.toFormula τ) (insert s.next U) (s.next + 1)
      (f (fresh s).1 (fresh s).2).2.next R) :
    Spec (((fresh >>= f) s).1.toFormula τ) U s.next ((fresh >>= f) s).2.next
      fun x => ∃ z, R (Function.update x s.next z) :=
  Spec.fresh h

theorem insert_lt {U : Set ℕ} {c : ℕ} (hU : ∀ i ∈ U, i < c) : ∀ i ∈ insert c U, i < c + 1 := by
  intro i hi
  rcases Set.mem_insert_iff.1 hi with rfl | hi
  · omega
  · have := hU i hi; omega

/-- Runs of a list of constructions with specifications. -/
theorem seqM_specL {τ : ExPoly} {U : Set ℕ} :
    ∀ (ms : List (NM NForm)) (Rs : List ((ℕ → ℕ) → Prop)),
      List.Forall₂ (fun m R => MSpec τ m U R) ms Rs →
      ∀ s : State, (∀ i ∈ U, i < s.next) →
        SpecL (((seqM ms) s).1.map (NForm.toFormula τ)) U s.next ((seqM ms) s).2.next
          fun x => ∀ R ∈ Rs, R x
  | [], [], _, s, _ => by simpa [seqM] using SpecL.nil U s.next
  | m :: ms, R :: Rs, h, s, hs => by
    rw [List.forall₂_cons] at h
    have h1 := h.1 s hs
    have h2 := seqM_specL ms Rs h.2 (m s).2 fun i hi => lt_of_lt_of_le (hs i hi) h1.le
    have := SpecL.cons h1 h2 hs
    simpa [seqM] using this

theorem MSpec.andM {τ : ExPoly} {U : Set ℕ} {ms : List (NM NForm)} {Rs : List ((ℕ → ℕ) → Prop)}
    (h : List.Forall₂ (fun m R => MSpec τ m U R) ms Rs) :
    MSpec τ (andM ms) U fun x => ∀ R ∈ Rs, R x := fun s hs => by
  have := (seqM_specL ms Rs h s hs).and
  simpa [Natural.andM, NForm.toFormula] using this

theorem seqM_specO {τ : ExPoly} {U : Set ℕ} :
    ∀ (ms : List (NM NForm)) (Rs : List ((ℕ → ℕ) → Prop)),
      List.Forall₂ (fun m R => MSpec τ m U R) ms Rs →
      ∀ s : State, (∀ i ∈ U, i < s.next) →
        SpecO (((seqM ms) s).1.map (NForm.toFormula τ)) U s.next ((seqM ms) s).2.next
          fun x => ∃ R ∈ Rs, R x
  | [], [], _, s, _ => by simpa [seqM] using SpecO.nil U s.next
  | m :: ms, R :: Rs, h, s, hs => by
    rw [List.forall₂_cons] at h
    have h1 := h.1 s hs
    have h2 := seqM_specO ms Rs h.2 (m s).2 fun i hi => lt_of_lt_of_le (hs i hi) h1.le
    have := SpecO.cons h1 h2 hs
    simpa [seqM] using this

theorem MSpec.orM {τ : ExPoly} {U : Set ℕ} {ms : List (NM NForm)} {Rs : List ((ℕ → ℕ) → Prop)}
    (h : List.Forall₂ (fun m R => MSpec τ m U R) ms Rs) :
    MSpec τ (orM ms) U fun x => ∃ R ∈ Rs, R x := fun s hs => by
  have := (seqM_specO ms Rs h s hs).or
  simpa [Natural.orM, NForm.toFormula] using this

/-! ### Power calls with private blocks (item 3) -/

/-- The natural relation of an existential polynomial at integer parameters: some natural
values of its witnesses make it vanish. -/
def ExNatRel (τ : ExPoly) (a : Fin τ.params → ℤ) : Prop :=
  ∃ y : Fin τ.witnesses → ℕ,
    ev (assign τ.params τ.witnesses (fun i => (a i : ℚ)) (fun j => (y j : ℚ))) τ.poly = 0

/-- The parameter values of a call at `x`. -/
def callVals (x : ℕ → ℕ) (P Q R : Poly) (p : ℕ) : Fin p → ℤ :=
  fun i => zv x (callArgs P Q R p i)

theorem vars_callArgs {P Q R : Poly} {p : ℕ} {S : ℕ → Prop} (hP : VarsIn P S) (hQ : VarsIn Q S)
    (hR : VarsIn R S) (i : Fin p) : VarsIn (callArgs P Q R p i) S := by
  unfold callArgs getPoly
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => exact hP
  | 1 => exact hQ
  | 2 => exact hR
  | n + 3 => simpa using VarsIn.zero S

/-- **Private power blocks** (item 3). A call atom of a well-formed template with `79`
witnesses on a fresh block may be replaced by the natural relation of the template at the
values of its parameter polynomials. -/
theorem callPower_spec {τ : ExPoly} (hτ : τ.WF) (hw : τ.witnesses = powerWitnesses)
    {P Q R : Ex} {U : Set ℕ} (hP : VarsIn P.poly (· ∈ U)) (hQ : VarsIn Q.poly (· ∈ U))
    (hR : VarsIn R.poly (· ∈ U)) :
    MSpec τ (callPower P Q R) U fun x => ExNatRel τ (callVals x P.poly Q.poly R.poly τ.params) := by
  intro s hs
  simp only [callPower, NForm.toFormula]
  have hg : ∀ k, VarsIn (callArgs P.poly Q.poly R.poly τ.params k) (· ∈ U) :=
    vars_callArgs hP hQ hR
  refine ⟨by omega, ?_, fun x => ?_⟩
  · intro i hi
    simp only [Formula.compile_call] at hi
    rcases mem_vars_callPoly hτ _ hi with ⟨k, hk⟩ | h
    · exact Or.inl (hg k i hk)
    · exact Or.inr ⟨h.1, by rw [hw] at h; exact h.2⟩
  · simp only [nholds_call]
    have hgU : ∀ k, ∀ i ∈ (callArgs P.poly Q.poly R.poly τ.params k).vars, i < s.next :=
      fun k i hi => hs i (hg k i hi)
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨fun j => y (s.next + j), ?_⟩
      rw [← Int.cast_eq_zero (α := ℚ), ← ev_qa, ExPoly.ev_call hτ] at h
      rw [← h]
      refine congrArg (fun a => ev a τ.poly) (funext fun i => ?_)
      unfold assign
      split_ifs with h1 h2
      · simp only [callVals, ← ev_qa]
        exact ev_congr fun l hl => by
          simp only [qa]
          rw [hy l (by have := hgU _ l hl; omega)]
      · simp [qa]
      · rfl
    · rintro ⟨w, hw'⟩
      let y : ℕ → ℕ := fun i =>
        if h : s.next ≤ i ∧ i - s.next < τ.witnesses then w ⟨i - s.next, h.2⟩ else x i
      refine ⟨y, fun i hi => ?_, ?_⟩
      · simp only [y]
        rw [dite_eq_right]
        rintro ⟨h1, h2⟩
        exact hi ⟨h1, by rw [hw] at h2; unfold powerWitnesses at h2 ⊢; omega⟩
      · rw [← Int.cast_eq_zero (α := ℚ), ← ev_qa, ExPoly.ev_call hτ, ← hw']
        refine congrArg (fun a => ev a τ.poly) (funext fun i => ?_)
        unfold assign
        split_ifs with h1 h2
        · simp only [callVals, ← ev_qa]
          exact ev_congr fun l hl => by
            simp only [qa, y]
            rw [dite_eq_right (by have := hgU _ l hl; omega)]
        · simp only [qa, y]
          rw [dite_eq_left ⟨by omega, by omega⟩]
          simp
        · rfl

end ZInQ.Compiler.Natural
