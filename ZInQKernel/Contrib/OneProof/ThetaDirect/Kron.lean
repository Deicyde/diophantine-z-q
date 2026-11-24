import ZInQKernel.Contrib.OneProof.H.TailZ19

/-! theta-direct: copied verbatim from origin/wip/theta-fold (8e3dbdea) `ZInQKernel/Contrib/OneProof/LinYangKron.lean`;
   only the import lines are changed (this base has no theta-fold modules). -/

/-! # theta-fold (1/4): igusa-alg's Kronecker evaluation engine

igusa-alg's `IgusaAlgEval` (scratch/igusa-alg/IgusaAlg.lean, verbatim through linyang-printed's
LinYangPrintedFull.lean): a homogeneous integer polynomial identity holds over every commutative ring once the
kernel checks one value at a Kronecker point and a coefficient bound (`Data.gen_eq_zero`; `decide +kernel`, no
`native_decide`). Used by `LinYangGlue` for the identities `IgusaAlg 3..9`. docs/research/theta-fold.md. -/

/-! # igusa-alg: polynomial identities by one Kronecker evaluation

A `PE` is a polynomial expression in four variables with integer coefficients. For an identity
`gen = 0` between such expressions (and the block elementary symmetric functions `E`) that is
homogeneous of degree `d`, we prove it over every commutative ring from a single kernel evaluation at
`(1, N, N^D, N^{D²})`, `D = d + 1`, together with a bound `M < N` for all coefficients (a majorant
computed at `(1,1,1,1)`): the Kronecker substitution is injective on homogeneous polynomials of
degree `d`, and an integer polynomial with coefficients of absolute value `< N` vanishing at `N` is
zero. -/

namespace IgusaAlgEval

open Polynomial

/-- Polynomial expressions in four variables with integer coefficients. -/
inductive PE : Type
  | v (i : Fin 4)
  | c (n : ℤ)
  | add (a b : PE)
  | mul (a b : PE)
  | pow (a : PE) (n : ℕ)

section Eval
variable {R S : Type*} [CommRing R] [CommRing S]

def sel (s0 s1 s2 s3 : R) (i : Fin 4) : R :=
  if i.val = 0 then s0 else if i.val = 1 then s1 else if i.val = 2 then s2 else s3

/-- Evaluation of a `PE` in a commutative ring. -/
def PE.eval (s0 s1 s2 s3 : R) : PE → R
  | .v i => sel s0 s1 s2 s3 i
  | .c n => (n : R)
  | .add a b => a.eval s0 s1 s2 s3 + b.eval s0 s1 s2 s3
  | .mul a b => a.eval s0 s1 s2 s3 * b.eval s0 s1 s2 s3
  | .pow a n => a.eval s0 s1 s2 s3 ^ n

/-- The majorant expression: all constants replaced by their absolute values. -/
def PE.abs : PE → PE
  | .v i => .v i
  | .c n => .c |n|
  | .add a b => .add a.abs b.abs
  | .mul a b => .mul a.abs b.abs
  | .pow a n => .pow a.abs n

/-- Homogeneous degree of a `PE` (syntactic). -/
def PE.hd : PE → Option ℕ
  | .v _ => some 1
  | .c _ => some 0
  | .add a b => if a.hd = b.hd then a.hd else none
  | .mul a b => match a.hd, b.hd with
    | some x, some y => some (x + y)
    | _, _ => none
  | .pow a n => match a.hd with
    | some x => some (n * x)
    | none => none

theorem map_sel (f : R →+* S) (s0 s1 s2 s3 : R) (i : Fin 4) :
    f (sel s0 s1 s2 s3 i) = sel (f s0) (f s1) (f s2) (f s3) i := by
  unfold sel; split_ifs <;> rfl

theorem PE.map_eval (f : R →+* S) (s0 s1 s2 s3 : R) (e : PE) :
    f (e.eval s0 s1 s2 s3) = e.eval (f s0) (f s1) (f s2) (f s3) := by
  induction e with
  | v i => exact map_sel f s0 s1 s2 s3 i
  | c n => simp [PE.eval]
  | add a b ha hb => simp [PE.eval, ha, hb]
  | mul a b ha hb => simp [PE.eval, ha, hb]
  | pow a n ha => simp [PE.eval, ha]

/-- `E bl j`: the coefficient of `T^j` in `∏_{(q,r) ∈ bl} (1 + qT + rT²)`. -/
def E : List (R × R) → ℕ → R
  | [], 0 => 1
  | [], _ + 1 => 0
  | (q, r) :: l, j => E l j + (if 1 ≤ j then q * E l (j - 1) else 0) +
      (if 2 ≤ j then r * E l (j - 2) else 0)

theorem map_E (f : R →+* S) (bl : List (R × R)) (j : ℕ) :
    f (E bl j) = E (bl.map fun p => (f p.1, f p.2)) j := by
  induction bl generalizing j with
  | nil => cases j <;> simp [E]
  | cons p l ih =>
    obtain ⟨q, r⟩ := p
    simp only [E, List.map_cons, map_add, apply_ite f, map_mul, map_zero, ih]

/-- Memoized version of `E` (coefficients `0..9`), used for kernel evaluation. -/
def stepV (q r : R) (v : List R) : List R :=
  (List.range 10).map fun j => v.getD j 0 + (if 1 ≤ j then q * v.getD (j - 1) 0 else 0) +
    (if 2 ≤ j then r * v.getD (j - 2) 0 else 0)

def EV : List (R × R) → List R
  | [] => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | (q, r) :: l => stepV q r (EV l)

theorem EV_getD (bl : List (R × R)) (j : ℕ) (hj : j < 10) : (EV bl).getD j 0 = E bl j := by
  induction bl generalizing j with
  | nil => interval_cases j <;> rfl
  | cons p l ih =>
    obtain ⟨q, r⟩ := p
    simp only [EV, stepV, E, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
      Option.map_some, Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, ih j hj]
    congr 1
    · congr 1
      split_ifs with h
      · rw [← List.getD_eq_getElem?_getD, ih (j - 1) (by omega)]
      · rfl
    · split_ifs with h
      · rw [← List.getD_eq_getElem?_getD, ih (j - 2) (by omega)]
      · rfl

end Eval

/-! ## Data of an identity -/

/-- An identity `dK · E_k(blocks) = rhs` of polynomial expressions. -/
structure Data where
  blocks : List (PE × PE)
  k : ℕ
  dK : ℤ
  rhs : PE

section Gen
variable {R S : Type*} [CommRing R] [CommRing S]

def evB (s0 s1 s2 s3 : R) (p : PE × PE) : R × R := (p.1.eval s0 s1 s2 s3, p.2.eval s0 s1 s2 s3)
def evBabs (s0 s1 s2 s3 : R) (p : PE × PE) : R × R :=
  (p.1.abs.eval s0 s1 s2 s3, p.2.abs.eval s0 s1 s2 s3)

def Data.gen (X : Data) (s0 s1 s2 s3 : R) : R :=
  (X.dK : R) * E (X.blocks.map (evB s0 s1 s2 s3)) X.k - X.rhs.eval s0 s1 s2 s3

def Data.genAbs (X : Data) (s0 s1 s2 s3 : R) : R :=
  ((|X.dK| : ℤ) : R) * E (X.blocks.map (evBabs s0 s1 s2 s3)) X.k + X.rhs.abs.eval s0 s1 s2 s3

def Data.genFast (X : Data) (s0 s1 s2 s3 : R) : R :=
  (X.dK : R) * (EV (X.blocks.map (evB s0 s1 s2 s3))).getD X.k 0 - X.rhs.eval s0 s1 s2 s3

theorem Data.genFast_eq (X : Data) (hk : X.k < 10) (s0 s1 s2 s3 : R) :
    X.genFast s0 s1 s2 s3 = X.gen s0 s1 s2 s3 := by
  simp only [Data.genFast, Data.gen, EV_getD _ _ hk]

theorem Data.map_gen (X : Data) (f : R →+* S) (s0 s1 s2 s3 : R) :
    f (X.gen s0 s1 s2 s3) = X.gen (f s0) (f s1) (f s2) (f s3) := by
  have hfun : ((fun p => (f p.1, f p.2)) ∘ evB s0 s1 s2 s3) = evB (f s0) (f s1) (f s2) (f s3) := by
    funext p; simp [evB, PE.map_eval]
  simp only [Data.gen, map_sub, map_mul, map_intCast, map_E, List.map_map, PE.map_eval, hfun]

theorem Data.map_genAbs (X : Data) (f : R →+* S) (s0 s1 s2 s3 : R) :
    f (X.genAbs s0 s1 s2 s3) = X.genAbs (f s0) (f s1) (f s2) (f s3) := by
  have hfun : ((fun p => (f p.1, f p.2)) ∘ evBabs s0 s1 s2 s3) =
      evBabs (f s0) (f s1) (f s2) (f s3) := by
    funext p; simp [evBabs, PE.map_eval]
  simp only [Data.genAbs, map_add, map_mul, map_intCast, map_E, List.map_map, PE.map_eval, hfun]

end Gen

/-! ## Homogeneity -/

section Hom
open MvPolynomial

abbrev MP := MvPolynomial (Fin 4) ℤ

theorem sel_X (i : Fin 4) : sel (X 0 : MP) (X 1) (X 2) (X 3) i = X i := by
  fin_cases i <;> rfl

theorem isHom_of_eq {φ : MP} {m n : ℕ} (h : φ.IsHomogeneous m) (e : m = n) : φ.IsHomogeneous n :=
  e ▸ h

theorem PE.isHom (e : PE) : ∀ d, e.hd = some d →
    (e.eval (X 0) (X 1) (X 2) (X 3) : MP).IsHomogeneous d := by
  induction e with
  | v i =>
    intro d h
    simp only [PE.hd, Option.some.injEq] at h
    subst h
    simp only [PE.eval, sel_X]
    exact isHomogeneous_X _ _
  | c n =>
    intro d h
    simp only [PE.hd, Option.some.injEq] at h
    subst h
    simp only [PE.eval]
    have : ((n : ℤ) : MP) = MvPolynomial.C n := by simp
    rw [this]; exact isHomogeneous_C _ _
  | add a b ha hb =>
    intro d h
    simp only [PE.hd] at h
    split_ifs at h with hab
    exact (ha d h).add (hb d (hab ▸ h))
  | mul a b ha hb =>
    intro d h
    simp only [PE.hd] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq] at h
      exact isHom_of_eq ((ha x hx).mul (hb y hy)) h
    · simp at h
  | pow a n ha =>
    intro d h
    simp only [PE.hd] at h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq] at h
      exact isHom_of_eq ((ha x hx).pow n) (by rw [← h, mul_comm])
    · simp at h

theorem E_isHom (bl : List (MP × MP)) (hbl : ∀ p ∈ bl, p.1.IsHomogeneous 4 ∧ p.2.IsHomogeneous 8) :
    ∀ j, (E bl j).IsHomogeneous (4 * j) := by
  induction bl with
  | nil => intro j; cases j
           · simpa [E] using isHomogeneous_one (Fin 4) ℤ
           · simpa [E] using isHomogeneous_zero (Fin 4) ℤ _
  | cons p l ih =>
    obtain ⟨q, r⟩ := p
    have hq := (hbl (q, r) (by simp)).1
    have hr := (hbl (q, r) (by simp)).2
    have ih := ih (fun p hp => hbl p (by simp [hp]))
    intro j
    simp only [E]
    refine ((ih j).add ?_).add ?_
    · split_ifs with h
      · exact isHom_of_eq (hq.mul (ih (j - 1))) (by omega)
      · exact isHomogeneous_zero (Fin 4) ℤ _
    · split_ifs with h
      · exact isHom_of_eq (hr.mul (ih (j - 2))) (by omega)
      · exact isHomogeneous_zero (Fin 4) ℤ _

theorem Data.gen_isHom (X : Data)
    (hblk : X.blocks.all (fun p => p.1.hd == some 4 && p.2.hd == some 8) = true)
    (hrhs : X.rhs.hd = some (4 * X.k)) :
    (X.gen (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) : MP).IsHomogeneous
      (4 * X.k) := by
  unfold Data.gen
  refine IsHomogeneous.sub ?_ (PE.isHom _ _ hrhs)
  have h0 : ((X.dK : ℤ) : MP) = MvPolynomial.C X.dK := by simp
  rw [h0]
  refine isHom_of_eq ((isHomogeneous_C _ _).mul (E_isHom _ ?_ X.k)) (by omega)
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
  have := List.all_eq_true.mp hblk b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨PE.isHom _ _ this.1, PE.isHom _ _ this.2⟩

end Hom

/-! ## Majorants of integer polynomials -/

section Maj

/-- `Maj p P`: every coefficient of `p` is bounded in absolute value by that of `P`. -/
def Maj (p P : ℤ[X]) : Prop := ∀ n, |p.coeff n| ≤ P.coeff n

theorem Maj.nonneg {p P : ℤ[X]} (h : Maj p P) (n : ℕ) : 0 ≤ P.coeff n := (abs_nonneg _).trans (h n)

theorem Maj.add {p q P Q : ℤ[X]} (hp : Maj p P) (hq : Maj q Q) : Maj (p + q) (P + Q) := fun n => by
  simp only [coeff_add]; exact (abs_add_le _ _).trans (add_le_add (hp n) (hq n))

theorem Maj.sub {p q P Q : ℤ[X]} (hp : Maj p P) (hq : Maj q Q) : Maj (p - q) (P + Q) := fun n => by
  simp only [coeff_sub, coeff_add]; exact (abs_sub _ _).trans (add_le_add (hp n) (hq n))

theorem Maj.mul {p q P Q : ℤ[X]} (hp : Maj p P) (hq : Maj q Q) : Maj (p * q) (P * Q) := fun n => by
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hp _) (hq _) (abs_nonneg _) (hp.nonneg _)

theorem maj_zero : Maj 0 0 := fun n => by simp

theorem maj_one : Maj 1 1 := fun n => by
  rw [coeff_one]; split_ifs <;> simp

theorem Maj.pow {p P : ℤ[X]} (hp : Maj p P) (n : ℕ) : Maj (p ^ n) (P ^ n) := by
  induction n with
  | zero => simpa using maj_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hp

theorem maj_intCast (c : ℤ) : Maj (c : ℤ[X]) ((|c| : ℤ) : ℤ[X]) := fun n => by
  rw [← C_eq_intCast, ← C_eq_intCast, coeff_C, coeff_C]; split_ifs <;> simp

theorem maj_X_pow (k : ℕ) : Maj (X ^ k) (X ^ k) := fun n => by
  rw [coeff_X_pow]; split_ifs <;> simp

theorem maj_sel {s0 s1 s2 s3 S0 S1 S2 S3 : ℤ[X]} (h0 : Maj s0 S0) (h1 : Maj s1 S1) (h2 : Maj s2 S2)
    (h3 : Maj s3 S3) (i : Fin 4) : Maj (sel s0 s1 s2 s3 i) (sel S0 S1 S2 S3 i) := by
  unfold sel; split_ifs <;> assumption

theorem PE.maj {s0 s1 s2 s3 S0 S1 S2 S3 : ℤ[X]} (h0 : Maj s0 S0) (h1 : Maj s1 S1) (h2 : Maj s2 S2)
    (h3 : Maj s3 S3) (e : PE) : Maj (e.eval s0 s1 s2 s3) (e.abs.eval S0 S1 S2 S3) := by
  induction e with
  | v i => exact maj_sel h0 h1 h2 h3 i
  | c n => exact maj_intCast n
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | pow a n ha => exact ha.pow n

theorem maj_ite {p P : ℤ[X]} (c : Prop) [Decidable c] (h : Maj p P) :
    Maj (if c then p else 0) (if c then P else 0) := by
  split_ifs
  · exact h
  · exact maj_zero

theorem E_maj {s0 s1 s2 s3 S0 S1 S2 S3 : ℤ[X]} (h0 : Maj s0 S0) (h1 : Maj s1 S1) (h2 : Maj s2 S2)
    (h3 : Maj s3 S3) (bs : List (PE × PE)) :
    ∀ j, Maj (E (bs.map (evB s0 s1 s2 s3)) j) (E (bs.map (evBabs S0 S1 S2 S3)) j) := by
  induction bs with
  | nil => intro j; cases j
           · simpa [E] using maj_one
           · simpa [E] using maj_zero
  | cons b l ih =>
    intro j
    simp only [List.map_cons, evB, evBabs, E]
    exact ((ih j).add (maj_ite _ ((b.1.maj h0 h1 h2 h3).mul (ih _)))).add
      (maj_ite _ ((b.2.maj h0 h1 h2 h3).mul (ih _)))

theorem Data.maj_gen (X : Data) {s0 s1 s2 s3 S0 S1 S2 S3 : ℤ[X]} (h0 : Maj s0 S0) (h1 : Maj s1 S1)
    (h2 : Maj s2 S2) (h3 : Maj s3 S3) :
    Maj (X.gen s0 s1 s2 s3) (X.genAbs S0 S1 S2 S3) :=
  ((maj_intCast X.dK).mul (E_maj h0 h1 h2 h3 X.blocks X.k)).sub (X.rhs.maj h0 h1 h2 h3)

theorem coeff_le_eval_one (P : ℤ[X]) (h : ∀ n, 0 ≤ P.coeff n) (n : ℕ) : P.coeff n ≤ P.eval 1 := by
  rw [eval_eq_sum, sum_def]
  simp only [one_pow, mul_one]
  by_cases hn : n ∈ P.support
  · exact Finset.single_le_sum (fun i _ => h i) hn
  · rw [notMem_support_iff.mp hn]; exact Finset.sum_nonneg fun i _ => h i

end Maj

/-! ## Base-`N` uniqueness and Kronecker injectivity -/

theorem eq_zero_of_eval_eq_zero_of_coeff_lt (N M : ℤ) (hMN : M < N)
    (p : ℤ[X]) (hc : ∀ n, |p.coeff n| ≤ M) (hp : p.eval N = 0) : p = 0 := by
  have hN : 0 < N := lt_of_le_of_lt ((abs_nonneg _).trans (hc 0)) hMN
  suffices ∀ m, ∀ p : ℤ[X], p.natDegree ≤ m → (∀ n, |p.coeff n| ≤ M) → p.eval N = 0 → p = 0 from
    this _ p le_rfl hc hp
  intro m
  induction m with
  | zero =>
    intro p hd _ he
    rw [eq_C_of_natDegree_le_zero hd] at he ⊢
    simpa using he
  | succ m ih =>
    intro p hd hc he
    have hsplit := X_mul_divX_add p
    have he' : N * (divX p).eval N + p.coeff 0 = 0 := by
      have := congrArg (eval N) hsplit; simpa [he] using this
    have h0 : p.coeff 0 = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N)
      · exact ⟨-(divX p).eval N, by linarith⟩
      · exact lt_of_le_of_lt (hc 0) hMN
    have hdiv : divX p = 0 := by
      apply ih
      · rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      · intro n; rw [coeff_divX]; exact hc _
      · rw [h0, add_zero] at he'
        exact (mul_eq_zero.mp he').resolve_left hN.ne'
    rw [← hsplit, hdiv, h0]; simp

theorem digits3 {D a b c a' b' c' : ℕ} (ha : a < D) (hb : b < D) (ha' : a' < D) (hb' : b' < D)
    (h : a + b * D + c * D ^ 2 = a' + b' * D + c' * D ^ 2) : a = a' ∧ b = b' ∧ c = c' := by
  have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le _) ha
  have e1 : a + D * (b + D * c) = a' + D * (b' + D * c') := by
    have : a + b * D + c * D ^ 2 = a + D * (b + D * c) := by ring
    have h' : a' + b' * D + c' * D ^ 2 = a' + D * (b' + D * c') := by ring
    rw [← this, ← h', h]
  have haa : a = a' := by
    have := congrArg (· % D) e1
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
    exact this
  subst haa
  have e2 : b + D * c = b' + D * c' := Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel e1)
  have hbb : b = b' := by
    have := congrArg (· % D) e2
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at this
    exact this
  subst hbb
  refine ⟨rfl, rfl, ?_⟩
  exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel e2)

section Kron
open MvPolynomial

/-- The Kronecker substitution `(X₀,X₁,X₂,X₃) ↦ (1, T, T^D, T^{D²})`. -/
noncomputable def kron (D : ℕ) : MP →ₐ[ℤ] ℤ[X] :=
  MvPolynomial.aeval (sel (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2)))

theorem sum_support_fin4 (m : Fin 4 →₀ ℕ) : ∑ i ∈ m.support, m i = m 0 + m 1 + m 2 + m 3 := by
  rw [Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)]
  simp [Fin.sum_univ_four]

theorem kron_monomial (D : ℕ) (m : Fin 4 →₀ ℕ) :
    ∏ i, (sel (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2)) i) ^ m i =
      Polynomial.X ^ (m 1 + m 2 * D + m 3 * D ^ 2) := by
  rw [Fin.prod_univ_four]
  have e0 : sel (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2)) 0 = 1 := rfl
  have e1 : sel (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2)) 1 =
    Polynomial.X := rfl
  have e2 : sel (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2)) 2 =
    Polynomial.X ^ D := rfl
  have e3 : sel (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2)) 3 =
    Polynomial.X ^ (D ^ 2) := rfl
  rw [e0, e1, e2, e3, one_pow, one_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1; ring

theorem kron_eq_zero (P : MP) (d : ℕ) (hP : P.IsHomogeneous d) (h : kron (d + 1) P = 0) : P = 0 := by
  by_contra hP0
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hP0
  have hmem : m ∈ P.support := mem_support_iff.mpr hm
  have key : ∀ m' ∈ P.support, m' 0 + m' 1 + m' 2 + m' 3 = d := fun m' hm' => by
    rw [← sum_support_fin4]; exact (hP.degree_eq_sum_deg_support hm').symm
  have hcoeff := congrArg (Polynomial.coeff · (m 1 + m 2 * (d + 1) + m 3 * (d + 1) ^ 2)) h
  simp only [kron, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Polynomial.coeff_zero,
    algebraMap_int_eq, eq_intCast] at hcoeff
  rw [Polynomial.finsetSum_coeff] at hcoeff
  simp only [kron_monomial, ← C_eq_intCast, Polynomial.coeff_C_mul_X_pow] at hcoeff
  rw [Finset.sum_eq_single m] at hcoeff
  · simp at hcoeff; exact hm hcoeff
  · intro m' hm' hne
    rw [if_neg]
    intro heq
    apply hne
    have k1 := key m hmem
    have k2 := key m' hm'
    obtain ⟨e1, e2, e3⟩ := digits3 (D := d + 1) (by omega) (by omega) (by omega) (by omega) heq
    ext i; fin_cases i
    · simp; omega
    · exact e1.symm
    · exact e2.symm
    · exact e3.symm
  · intro h'; exact absurd hmem h'

end Kron

/-! ## Main theorem -/

theorem Data.gen_eq_zero (X : Data) (N : ℕ)
    (hblk : X.blocks.all (fun p => p.1.hd == some 4 && p.2.hd == some 8) = true)
    (hrhs : X.rhs.hd = some (4 * X.k)) (hk : X.k < 10)
    (hM : X.genAbs (1 : ℤ) 1 1 1 < N)
    (hval : X.genFast (1 : ℤ) N ((N : ℤ) ^ (4 * X.k + 1)) ((N : ℤ) ^ ((4 * X.k + 1) ^ 2)) = 0)
    {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : X.gen s0 s1 s2 s3 = 0 := by
  set P : MP := X.gen (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)
  have hP := X.gen_isHom hblk hrhs
  set D := 4 * X.k + 1
  have hH : kron D P = X.gen (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2)) := by
    have := X.map_gen (kron D).toRingHom (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
      (MvPolynomial.X 3)
    simpa [kron, sel] using this
  have hmaj := X.maj_gen (s0 := (1 : ℤ[X])) (s1 := Polynomial.X) (s2 := Polynomial.X ^ D)
    (s3 := Polynomial.X ^ (D ^ 2)) maj_one (by simpa using maj_X_pow 1) (maj_X_pow D) (maj_X_pow _)
  have hev1 : (X.genAbs (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2))).eval 1 =
      X.genAbs (1 : ℤ) 1 1 1 := by
    have := X.map_genAbs (Polynomial.evalRingHom 1) (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D)
      (Polynomial.X ^ (D ^ 2))
    simpa using this
  have hevN : (X.gen (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D) (Polynomial.X ^ (D ^ 2))).eval (N : ℤ) =
      0 := by
    have := X.map_gen (Polynomial.evalRingHom (N : ℤ)) (1 : ℤ[X]) Polynomial.X (Polynomial.X ^ D)
      (Polynomial.X ^ (D ^ 2))
    simp only [coe_evalRingHom, eval_one, eval_X, eval_pow] at this
    rw [this, ← X.genFast_eq hk]; exact hval
  have hzero : kron D P = 0 := by
    rw [hH]
    refine eq_zero_of_eval_eq_zero_of_coeff_lt (N : ℤ) (X.genAbs (1 : ℤ) 1 1 1) hM _ ?_ hevN
    intro n
    refine (hmaj n).trans ?_
    rw [← hev1]
    exact coeff_le_eval_one _ hmaj.nonneg n
  have hP0 : P = 0 := kron_eq_zero P (4 * X.k) hP hzero
  have := X.map_gen (MvPolynomial.aeval (sel s0 s1 s2 s3)).toRingHom (MvPolynomial.X 0 : MP)
    (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)
  rw [show X.gen (MvPolynomial.X 0 : MP) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) = P
    from rfl, hP0, map_zero] at this
  simpa [sel] using this.symm


theorem PE.eval_v0 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 0 = s0 := rfl
theorem PE.eval_v1 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 1 = s1 := rfl
theorem PE.eval_v2 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 2 = s2 := rfl
theorem PE.eval_v3 {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : sel s0 s1 s2 s3 3 = s3 := rfl

/-- `Ψ₄ = 4ψ₄` in `s_i = U_i²`. -/
def psi4E : PE := (.add (.add (.add (.mul (.c (4)) (.pow (.v 0) 4)) (.mul (.c (56)) (.mul (.pow (.v 0) 2) (.pow (.v 1) 2)))) (.add (.mul (.c (56)) (.mul (.pow (.v 0) 2) (.pow (.v 2) 2))) (.add (.mul (.c (56)) (.mul (.pow (.v 0) 2) (.pow (.v 3) 2))) (.mul (.c (672)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3)))))))) (.add (.add (.mul (.c (4)) (.pow (.v 1) 4)) (.add (.mul (.c (56)) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2))) (.mul (.c (56)) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2))))) (.add (.mul (.c (4)) (.pow (.v 2) 4)) (.add (.mul (.c (56)) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))) (.mul (.c (4)) (.pow (.v 3) 4))))))

/-- `Ψ₆ = 4ψ₆` in `s_i = U_i²`. -/
def psi6E : PE := (.add (.add (.add (.add (.mul (.c (4)) (.pow (.v 0) 6)) (.add (.mul (.c (-132)) (.mul (.pow (.v 0) 4) (.pow (.v 1) 2))) (.mul (.c (-132)) (.mul (.pow (.v 0) 4) (.pow (.v 2) 2))))) (.add (.mul (.c (-132)) (.mul (.pow (.v 0) 4) (.pow (.v 3) 2))) (.add (.mul (.c (3168)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.mul (.c (-132)) (.mul (.pow (.v 0) 2) (.pow (.v 1) 4)))))) (.add (.add (.mul (.c (1320)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2)))) (.add (.mul (.c (1320)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2)))) (.mul (.c (-132)) (.mul (.pow (.v 0) 2) (.pow (.v 2) 4))))) (.add (.mul (.c (1320)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (-132)) (.mul (.pow (.v 0) 2) (.pow (.v 3) 4))) (.mul (.c (3168)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.v 3))))))))) (.add (.add (.add (.mul (.c (3168)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.v 3))))) (.add (.mul (.c (3168)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 3))))) (.mul (.c (4)) (.pow (.v 1) 6)))) (.add (.mul (.c (-132)) (.mul (.pow (.v 1) 4) (.pow (.v 2) 2))) (.add (.mul (.c (-132)) (.mul (.pow (.v 1) 4) (.pow (.v 3) 2))) (.mul (.c (-132)) (.mul (.pow (.v 1) 2) (.pow (.v 2) 4)))))) (.add (.add (.mul (.c (1320)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (-132)) (.mul (.pow (.v 1) 2) (.pow (.v 3) 4))) (.mul (.c (4)) (.pow (.v 2) 6)))) (.add (.mul (.c (-132)) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2))) (.add (.mul (.c (-132)) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4))) (.mul (.c (4)) (.pow (.v 3) 6)))))))

/-- `X₁₀ = ∏ θ_m² = -2¹⁴χ₁₀` in `s_i = U_i²`. -/
def x10E : PE := (.add (.add (.add (.add (.add (.mul (.c (64)) (.mul (.pow (.v 0) 7) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2)))) (.mul (.c (-64)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2)))))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 5) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.v 3))))) (.mul (.c (-64)) (.mul (.pow (.v 0) 5) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.v 3)))))))) (.add (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 5) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 3))))) (.add (.mul (.c (128)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 4) (.pow (.v 2) 2)))) (.mul (.c (128)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 4) (.pow (.v 3) 2)))))) (.add (.mul (.c (128)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 2) (.pow (.v 2) 4)))) (.add (.mul (.c (832)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))))) (.mul (.c (128)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 2) (.pow (.v 3) 4)))))))) (.add (.add (.add (.mul (.c (128)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2)))) (.add (.mul (.c (128)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4)))) (.mul (.c (-64)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 5) (.mul (.v 2) (.v 3))))))) (.add (.mul (.c (-896)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 3) (.v 3))))) (.add (.mul (.c (-896)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.pow (.v 3) 3))))) (.mul (.c (-64)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.pow (.v 2) 5) (.v 3)))))))) (.add (.add (.mul (.c (-896)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.pow (.v 3) 3))))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 5))))) (.mul (.c (-64)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 6) (.pow (.v 2) 2)))))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 6) (.pow (.v 3) 2)))) (.add (.mul (.c (128)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 4) (.pow (.v 2) 4)))) (.mul (.c (832)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))))))))) (.add (.add (.add (.add (.mul (.c (128)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 4) (.pow (.v 3) 4)))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.pow (.v 2) 6)))) (.mul (.c (832)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2))))))) (.add (.mul (.c (832)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4))))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.pow (.v 3) 6)))) (.mul (.c (-64)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 6) (.pow (.v 3) 2))))))) (.add (.add (.mul (.c (128)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 4) (.pow (.v 3) 4)))) (.add (.mul (.c (-64)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 6)))) (.mul (.c (64)) (.mul (.v 0) (.mul (.pow (.v 1) 7) (.mul (.v 2) (.v 3))))))) (.add (.mul (.c (-64)) (.mul (.v 0) (.mul (.pow (.v 1) 5) (.mul (.pow (.v 2) 3) (.v 3))))) (.add (.mul (.c (-64)) (.mul (.v 0) (.mul (.pow (.v 1) 5) (.mul (.v 2) (.pow (.v 3) 3))))) (.mul (.c (-64)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 5) (.v 3))))))))) (.add (.add (.add (.mul (.c (-896)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 3) (.pow (.v 3) 3))))) (.add (.mul (.c (-64)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.pow (.v 3) 5))))) (.mul (.c (64)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 7) (.v 3))))))) (.add (.mul (.c (-64)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 5) (.pow (.v 3) 3))))) (.add (.mul (.c (-64)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.pow (.v 3) 5))))) (.mul (.c (64)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 7)))))))) (.add (.add (.mul (.c (-64)) (.mul (.pow (.v 1) 6) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (128)) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2)))) (.mul (.c (128)) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4)))))) (.add (.mul (.c (-64)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 6) (.pow (.v 3) 2)))) (.add (.mul (.c (128)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 4) (.pow (.v 3) 4)))) (.mul (.c (-64)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 6))))))))))

def x12E0 : PE := (.add (.add (.add (.add (.mul (.c (512)) (.mul (.pow (.v 0) 9) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.mul (.c (1024)) (.mul (.pow (.v 0) 8) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2))))) (.add (.mul (.c (1024)) (.mul (.pow (.v 0) 8) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (1024)) (.mul (.pow (.v 0) 8) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))) (.mul (.c (-6144)) (.mul (.pow (.v 0) 7) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.v 3)))))))) (.add (.add (.mul (.c (-6144)) (.mul (.pow (.v 0) 7) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.v 3))))) (.add (.mul (.c (-6144)) (.mul (.pow (.v 0) 7) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 3))))) (.mul (.c (-1024)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 1) 4) (.pow (.v 2) 2)))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 1) 4) (.pow (.v 3) 2)))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 1) 2) (.pow (.v 2) 4)))) (.mul (.c (38912)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))))))))) (.add (.add (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 1) 2) (.pow (.v 3) 4)))) (.mul (.c (-1024)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 6) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4)))) (.add (.mul (.c (11264)) (.mul (.pow (.v 0) 5) (.mul (.pow (.v 1) 5) (.mul (.v 2) (.v 3))))) (.mul (.c (-26624)) (.mul (.pow (.v 0) 5) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 3) (.v 3)))))))) (.add (.add (.mul (.c (-26624)) (.mul (.pow (.v 0) 5) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.pow (.v 3) 3))))) (.add (.mul (.c (11264)) (.mul (.pow (.v 0) 5) (.mul (.v 1) (.mul (.pow (.v 2) 5) (.v 3))))) (.mul (.c (-26624)) (.mul (.pow (.v 0) 5) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.pow (.v 3) 3))))))) (.add (.mul (.c (11264)) (.mul (.pow (.v 0) 5) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 5))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 6) (.pow (.v 2) 2)))) (.mul (.c (-1024)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 6) (.pow (.v 3) 2)))))))))

def x12E1 : PE := (.add (.add (.add (.add (.mul (.c (18432)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 4) (.pow (.v 2) 4)))) (.mul (.c (18432)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))))) (.add (.mul (.c (18432)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 4) (.pow (.v 3) 4)))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 2) (.pow (.v 2) 6)))) (.mul (.c (18432)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2)))))))) (.add (.add (.mul (.c (18432)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 1) 2) (.pow (.v 3) 6)))) (.mul (.c (-1024)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 2) 6) (.pow (.v 3) 2)))))) (.add (.mul (.c (18432)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 2) 4) (.pow (.v 3) 4)))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 4) (.mul (.pow (.v 2) 2) (.pow (.v 3) 6)))) (.mul (.c (-6144)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 7) (.mul (.v 2) (.v 3))))))))) (.add (.add (.add (.mul (.c (-26624)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 5) (.mul (.pow (.v 2) 3) (.v 3))))) (.mul (.c (-26624)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 5) (.mul (.v 2) (.pow (.v 3) 3)))))) (.add (.mul (.c (-26624)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 5) (.v 3))))) (.add (.mul (.c (-4096)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 3) (.pow (.v 3) 3))))) (.mul (.c (-26624)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.pow (.v 3) 5)))))))) (.add (.add (.mul (.c (-6144)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.pow (.v 2) 7) (.v 3))))) (.add (.mul (.c (-26624)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.pow (.v 2) 5) (.pow (.v 3) 3))))) (.mul (.c (-26624)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.pow (.v 3) 5))))))) (.add (.mul (.c (-6144)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 7))))) (.add (.mul (.c (1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 8) (.pow (.v 2) 2)))) (.mul (.c (1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 8) (.pow (.v 3) 2)))))))))

def x12E2 : PE := (.add (.add (.add (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 6) (.pow (.v 2) 4)))) (.mul (.c (38912)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 6) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 6) (.pow (.v 3) 4)))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 4) (.pow (.v 2) 6)))) (.mul (.c (18432)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2)))))))) (.add (.add (.mul (.c (18432)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 4) (.pow (.v 3) 6)))) (.mul (.c (1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.pow (.v 2) 8)))))) (.add (.mul (.c (38912)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 6) (.pow (.v 3) 2))))) (.add (.mul (.c (18432)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 4) (.pow (.v 3) 4))))) (.mul (.c (38912)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 6))))))))) (.add (.add (.add (.mul (.c (1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.pow (.v 3) 8)))) (.mul (.c (1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 8) (.pow (.v 3) 2))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 6) (.pow (.v 3) 4)))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 4) (.pow (.v 3) 6)))) (.mul (.c (1024)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 8))))))) (.add (.add (.mul (.c (512)) (.mul (.v 0) (.mul (.pow (.v 1) 9) (.mul (.v 2) (.v 3))))) (.add (.mul (.c (-6144)) (.mul (.v 0) (.mul (.pow (.v 1) 7) (.mul (.pow (.v 2) 3) (.v 3))))) (.mul (.c (-6144)) (.mul (.v 0) (.mul (.pow (.v 1) 7) (.mul (.v 2) (.pow (.v 3) 3))))))) (.add (.mul (.c (11264)) (.mul (.v 0) (.mul (.pow (.v 1) 5) (.mul (.pow (.v 2) 5) (.v 3))))) (.add (.mul (.c (-26624)) (.mul (.v 0) (.mul (.pow (.v 1) 5) (.mul (.pow (.v 2) 3) (.pow (.v 3) 3))))) (.mul (.c (11264)) (.mul (.v 0) (.mul (.pow (.v 1) 5) (.mul (.v 2) (.pow (.v 3) 5))))))))))

def x12E3 : PE := (.add (.add (.add (.add (.mul (.c (-6144)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 7) (.v 3))))) (.mul (.c (-26624)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 5) (.pow (.v 3) 3)))))) (.add (.mul (.c (-26624)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 3) (.pow (.v 3) 5))))) (.mul (.c (-6144)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.pow (.v 3) 7))))))) (.add (.add (.mul (.c (512)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 9) (.v 3))))) (.mul (.c (-6144)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 7) (.pow (.v 3) 3)))))) (.add (.mul (.c (11264)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 5) (.pow (.v 3) 5))))) (.add (.mul (.c (-6144)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.pow (.v 3) 7))))) (.mul (.c (512)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 9))))))))) (.add (.add (.add (.mul (.c (1024)) (.mul (.pow (.v 1) 8) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))) (.mul (.c (-1024)) (.mul (.pow (.v 1) 6) (.mul (.pow (.v 2) 4) (.pow (.v 3) 2))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 1) 6) (.mul (.pow (.v 2) 2) (.pow (.v 3) 4)))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 6) (.pow (.v 3) 2)))) (.mul (.c (18432)) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 4) (.pow (.v 3) 4))))))) (.add (.add (.mul (.c (-1024)) (.mul (.pow (.v 1) 4) (.mul (.pow (.v 2) 2) (.pow (.v 3) 6)))) (.mul (.c (1024)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 8) (.pow (.v 3) 2))))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 6) (.pow (.v 3) 4)))) (.add (.mul (.c (-1024)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 4) (.pow (.v 3) 6)))) (.mul (.c (1024)) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 8)))))))))

/-- `X₁₂ = 2¹⁷·3·χ₁₂` in `s_i = U_i²`. -/
def x12E : PE := (.add (.add x12E0 x12E1) (.add x12E2 x12E3))

def blkQ0 : PE := (.add (.add (.add (.add (.add (.pow (.v 0) 4) (.mul (.c (4)) (.mul (.pow (.v 0) 3) (.v 1)))) (.add (.mul (.c (4)) (.mul (.pow (.v 0) 3) (.v 2))) (.mul (.c (4)) (.mul (.pow (.v 0) 3) (.v 3))))) (.add (.add (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 1) 2))) (.mul (.c (12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 2))))) (.add (.mul (.c (12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 2) 2)))))) (.add (.add (.add (.mul (.c (12)) (.mul (.pow (.v 0) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (4)) (.mul (.v 0) (.pow (.v 1) 3))) (.mul (.c (12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 2)))))) (.add (.add (.mul (.c (12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 3)))) (.mul (.c (12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 2) 2))))) (.add (.mul (.c (24)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.add (.mul (.c (12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 3) 2)))) (.mul (.c (4)) (.mul (.v 0) (.pow (.v 2) 3)))))))) (.add (.add (.add (.add (.mul (.c (12)) (.mul (.v 0) (.mul (.pow (.v 2) 2) (.v 3)))) (.mul (.c (12)) (.mul (.v 0) (.mul (.v 2) (.pow (.v 3) 2))))) (.add (.mul (.c (4)) (.mul (.v 0) (.pow (.v 3) 3))) (.pow (.v 1) 4))) (.add (.add (.mul (.c (4)) (.mul (.pow (.v 1) 3) (.v 2))) (.mul (.c (4)) (.mul (.pow (.v 1) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2))) (.add (.mul (.c (12)) (.mul (.pow (.v 1) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2))))))) (.add (.add (.add (.mul (.c (4)) (.mul (.v 1) (.pow (.v 2) 3))) (.mul (.c (12)) (.mul (.v 1) (.mul (.pow (.v 2) 2) (.v 3))))) (.add (.mul (.c (12)) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 2)))) (.mul (.c (4)) (.mul (.v 1) (.pow (.v 3) 3))))) (.add (.add (.pow (.v 2) 4) (.mul (.c (4)) (.mul (.pow (.v 2) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))) (.add (.mul (.c (4)) (.mul (.v 2) (.pow (.v 3) 3))) (.pow (.v 3) 4)))))))

def blkR0 : PE := (.mul (.c 0) (.pow (.v 0) 8))

def blkQ1 : PE := (.add (.add (.add (.add (.add (.pow (.v 0) 4) (.mul (.c (-4)) (.mul (.pow (.v 0) 3) (.v 1)))) (.add (.mul (.c (4)) (.mul (.pow (.v 0) 3) (.v 2))) (.mul (.c (-4)) (.mul (.pow (.v 0) 3) (.v 3))))) (.add (.add (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 1) 2))) (.mul (.c (-12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 2))))) (.add (.mul (.c (12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 2) 2)))))) (.add (.add (.add (.mul (.c (-12)) (.mul (.pow (.v 0) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (-4)) (.mul (.v 0) (.pow (.v 1) 3))) (.mul (.c (12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 2)))))) (.add (.add (.mul (.c (-12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 3)))) (.mul (.c (-12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 2) 2))))) (.add (.mul (.c (24)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.add (.mul (.c (-12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 3) 2)))) (.mul (.c (4)) (.mul (.v 0) (.pow (.v 2) 3)))))))) (.add (.add (.add (.add (.mul (.c (-12)) (.mul (.v 0) (.mul (.pow (.v 2) 2) (.v 3)))) (.mul (.c (12)) (.mul (.v 0) (.mul (.v 2) (.pow (.v 3) 2))))) (.add (.mul (.c (-4)) (.mul (.v 0) (.pow (.v 3) 3))) (.pow (.v 1) 4))) (.add (.add (.mul (.c (-4)) (.mul (.pow (.v 1) 3) (.v 2))) (.mul (.c (4)) (.mul (.pow (.v 1) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2))) (.add (.mul (.c (-12)) (.mul (.pow (.v 1) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2))))))) (.add (.add (.add (.mul (.c (-4)) (.mul (.v 1) (.pow (.v 2) 3))) (.mul (.c (12)) (.mul (.v 1) (.mul (.pow (.v 2) 2) (.v 3))))) (.add (.mul (.c (-12)) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 2)))) (.mul (.c (4)) (.mul (.v 1) (.pow (.v 3) 3))))) (.add (.add (.pow (.v 2) 4) (.mul (.c (-4)) (.mul (.pow (.v 2) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))) (.add (.mul (.c (-4)) (.mul (.v 2) (.pow (.v 3) 3))) (.pow (.v 3) 4)))))))

def blkR1 : PE := (.mul (.c 0) (.pow (.v 0) 8))

def blkQ2 : PE := (.add (.add (.add (.add (.add (.pow (.v 0) 4) (.mul (.c (4)) (.mul (.pow (.v 0) 3) (.v 1)))) (.add (.mul (.c (-4)) (.mul (.pow (.v 0) 3) (.v 2))) (.mul (.c (-4)) (.mul (.pow (.v 0) 3) (.v 3))))) (.add (.add (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 1) 2))) (.mul (.c (-12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 2))))) (.add (.mul (.c (-12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 2) 2)))))) (.add (.add (.add (.mul (.c (12)) (.mul (.pow (.v 0) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (4)) (.mul (.v 0) (.pow (.v 1) 3))) (.mul (.c (-12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 2)))))) (.add (.add (.mul (.c (-12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 3)))) (.mul (.c (12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 2) 2))))) (.add (.mul (.c (24)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.add (.mul (.c (12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 3) 2)))) (.mul (.c (-4)) (.mul (.v 0) (.pow (.v 2) 3)))))))) (.add (.add (.add (.add (.mul (.c (-12)) (.mul (.v 0) (.mul (.pow (.v 2) 2) (.v 3)))) (.mul (.c (-12)) (.mul (.v 0) (.mul (.v 2) (.pow (.v 3) 2))))) (.add (.mul (.c (-4)) (.mul (.v 0) (.pow (.v 3) 3))) (.pow (.v 1) 4))) (.add (.add (.mul (.c (-4)) (.mul (.pow (.v 1) 3) (.v 2))) (.mul (.c (-4)) (.mul (.pow (.v 1) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2))) (.add (.mul (.c (12)) (.mul (.pow (.v 1) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2))))))) (.add (.add (.add (.mul (.c (-4)) (.mul (.v 1) (.pow (.v 2) 3))) (.mul (.c (-12)) (.mul (.v 1) (.mul (.pow (.v 2) 2) (.v 3))))) (.add (.mul (.c (-12)) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 2)))) (.mul (.c (-4)) (.mul (.v 1) (.pow (.v 3) 3))))) (.add (.add (.pow (.v 2) 4) (.mul (.c (4)) (.mul (.pow (.v 2) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))) (.add (.mul (.c (4)) (.mul (.v 2) (.pow (.v 3) 3))) (.pow (.v 3) 4)))))))

def blkR2 : PE := (.mul (.c 0) (.pow (.v 0) 8))

def blkQ3 : PE := (.add (.add (.add (.add (.add (.pow (.v 0) 4) (.mul (.c (-4)) (.mul (.pow (.v 0) 3) (.v 1)))) (.add (.mul (.c (-4)) (.mul (.pow (.v 0) 3) (.v 2))) (.mul (.c (4)) (.mul (.pow (.v 0) 3) (.v 3))))) (.add (.add (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 1) 2))) (.mul (.c (12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 2))))) (.add (.mul (.c (-12)) (.mul (.pow (.v 0) 2) (.mul (.v 1) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 2) 2)))))) (.add (.add (.add (.mul (.c (-12)) (.mul (.pow (.v 0) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 0) 2) (.pow (.v 3) 2)))) (.add (.mul (.c (-4)) (.mul (.v 0) (.pow (.v 1) 3))) (.mul (.c (-12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 2)))))) (.add (.add (.mul (.c (12)) (.mul (.v 0) (.mul (.pow (.v 1) 2) (.v 3)))) (.mul (.c (-12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 2) 2))))) (.add (.mul (.c (24)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.add (.mul (.c (-12)) (.mul (.v 0) (.mul (.v 1) (.pow (.v 3) 2)))) (.mul (.c (-4)) (.mul (.v 0) (.pow (.v 2) 3)))))))) (.add (.add (.add (.add (.mul (.c (12)) (.mul (.v 0) (.mul (.pow (.v 2) 2) (.v 3)))) (.mul (.c (-12)) (.mul (.v 0) (.mul (.v 2) (.pow (.v 3) 2))))) (.add (.mul (.c (4)) (.mul (.v 0) (.pow (.v 3) 3))) (.pow (.v 1) 4))) (.add (.add (.mul (.c (4)) (.mul (.pow (.v 1) 3) (.v 2))) (.mul (.c (-4)) (.mul (.pow (.v 1) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2))) (.add (.mul (.c (-12)) (.mul (.pow (.v 1) 2) (.mul (.v 2) (.v 3)))) (.mul (.c (6)) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2))))))) (.add (.add (.add (.mul (.c (4)) (.mul (.v 1) (.pow (.v 2) 3))) (.mul (.c (-12)) (.mul (.v 1) (.mul (.pow (.v 2) 2) (.v 3))))) (.add (.mul (.c (12)) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 2)))) (.mul (.c (-4)) (.mul (.v 1) (.pow (.v 3) 3))))) (.add (.add (.pow (.v 2) 4) (.mul (.c (-4)) (.mul (.pow (.v 2) 3) (.v 3)))) (.add (.mul (.c (6)) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))) (.add (.mul (.c (-4)) (.mul (.v 2) (.pow (.v 3) 3))) (.pow (.v 3) 4)))))))

def blkR3 : PE := (.mul (.c 0) (.pow (.v 0) 8))

def blkQ4 : PE := (.add (.mul (.c (32)) (.mul (.pow (.v 0) 2) (.pow (.v 1) 2))) (.add (.mul (.c (192)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.mul (.c (32)) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2)))))

def blkR4 : PE := (.add (.add (.mul (.c (256)) (.mul (.pow (.v 0) 4) (.pow (.v 1) 4))) (.mul (.c (-1024)) (.mul (.pow (.v 0) 3) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.v 3)))))) (.add (.mul (.c (1536)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))))) (.add (.mul (.c (-1024)) (.mul (.v 0) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.pow (.v 3) 3))))) (.mul (.c (256)) (.mul (.pow (.v 2) 4) (.pow (.v 3) 4))))))

def blkQ5 : PE := (.add (.mul (.c (32)) (.mul (.pow (.v 0) 2) (.pow (.v 2) 2))) (.add (.mul (.c (192)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.mul (.c (32)) (.mul (.pow (.v 1) 2) (.pow (.v 3) 2)))))

def blkR5 : PE := (.add (.add (.mul (.c (256)) (.mul (.pow (.v 0) 4) (.pow (.v 2) 4))) (.mul (.c (-1024)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.pow (.v 2) 3) (.v 3)))))) (.add (.mul (.c (1536)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))))) (.add (.mul (.c (-1024)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.v 2) (.pow (.v 3) 3))))) (.mul (.c (256)) (.mul (.pow (.v 1) 4) (.pow (.v 3) 4))))))

def blkQ6 : PE := (.add (.mul (.c (32)) (.mul (.pow (.v 0) 2) (.pow (.v 3) 2))) (.add (.mul (.c (192)) (.mul (.v 0) (.mul (.v 1) (.mul (.v 2) (.v 3))))) (.mul (.c (32)) (.mul (.pow (.v 1) 2) (.pow (.v 2) 2)))))

def blkR6 : PE := (.add (.add (.mul (.c (256)) (.mul (.pow (.v 0) 4) (.pow (.v 3) 4))) (.mul (.c (-1024)) (.mul (.pow (.v 0) 3) (.mul (.v 1) (.mul (.v 2) (.pow (.v 3) 3)))))) (.add (.mul (.c (1536)) (.mul (.pow (.v 0) 2) (.mul (.pow (.v 1) 2) (.mul (.pow (.v 2) 2) (.pow (.v 3) 2))))) (.add (.mul (.c (-1024)) (.mul (.v 0) (.mul (.pow (.v 1) 3) (.mul (.pow (.v 2) 3) (.v 3))))) (.mul (.c (256)) (.mul (.pow (.v 1) 4) (.pow (.v 2) 4))))))

def blocksPE : List (PE × PE) := [(blkQ0, blkR0), (blkQ1, blkR1), (blkQ2, blkR2), (blkQ3, blkR3), (blkQ4, blkR4), (blkQ5, blkR5), (blkQ6, blkR6)]

/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = 3. -/
def rhsE3 : PE := (.add (.mul (.c (29)) (.pow psi4E 3)) (.add (.mul (.c (-8)) (.pow psi6E 2)) (.mul (.c (1188)) x12E)))

def dK3 : ℤ := 432

def data3 : Data := ⟨blocksPE, 3, dK3, rhsE3⟩

/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = 3, over every commutative ring. -/
theorem gen3_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data3.gen s0 s1 s2 s3 = 0 :=
  data3.gen_eq_zero (2 ^ 40) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3

/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = 4. -/
def rhsE4 : PE := (.add (.add (.mul (.c (43)) (.pow psi4E 4)) (.mul (.c (-64)) (.mul psi4E (.pow psi6E 2)))) (.add (.mul (.c (6624)) (.mul psi4E x12E)) (.mul (.c (9216)) (.mul psi6E x10E))))

def dK4 : ℤ := 6912

def data4 : Data := ⟨blocksPE, 4, dK4, rhsE4⟩

/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = 4, over every commutative ring. -/
theorem gen4_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data4.gen s0 s1 s2 s3 = 0 :=
  data4.gen_eq_zero (2 ^ 52) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3

/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = 5. -/
def rhsE5 : PE := (.add (.add (.mul (.c (1)) (.pow psi4E 5)) (.mul (.c (-4)) (.mul (.pow psi4E 2) (.pow psi6E 2)))) (.add (.mul (.c (450)) (.mul (.pow psi4E 2) x12E)) (.add (.mul (.c (-576)) (.mul psi4E (.mul psi6E x10E))) (.mul (.c (425088)) (.pow x10E 2)))))

def dK5 : ℤ := 3456

def data5 : Data := ⟨blocksPE, 5, dK5, rhsE5⟩

/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = 5, over every commutative ring. -/
theorem gen5_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data5.gen s0 s1 s2 s3 = 0 :=
  data5.gen_eq_zero (2 ^ 58) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3

/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = 6. -/
def rhsE6 : PE := (.add (.add (.add (.mul (.c (1)) (.pow psi4E 6)) (.mul (.c (-8)) (.mul (.pow psi4E 3) (.pow psi6E 2)))) (.add (.mul (.c (1512)) (.mul (.pow psi4E 3) x12E)) (.mul (.c (-7776)) (.mul (.pow psi4E 2) (.mul psi6E x10E))))) (.add (.add (.mul (.c (2923776)) (.mul psi4E (.pow x10E 2))) (.mul (.c (16)) (.pow psi6E 4))) (.add (.mul (.c (-2160)) (.mul (.pow psi6E 2) x12E)) (.mul (.c (41796)) (.pow x12E 2)))))

def dK6 : ℤ := 186624

def data6 : Data := ⟨blocksPE, 6, dK6, rhsE6⟩

/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = 6, over every commutative ring. -/
theorem gen6_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data6.gen s0 s1 s2 s3 = 0 :=
  data6.gen_eq_zero (2 ^ 70) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3

/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = 7. -/
def rhsE7 : PE := (.add (.add (.mul (.c (1)) (.mul (.pow psi4E 4) x12E)) (.add (.mul (.c (-8)) (.mul (.pow psi4E 3) (.mul psi6E x10E))) (.mul (.c (2952)) (.mul (.pow psi4E 2) (.pow x10E 2))))) (.add (.add (.mul (.c (-4)) (.mul psi4E (.mul (.pow psi6E 2) x12E))) (.mul (.c (198)) (.mul psi4E (.pow x12E 2)))) (.add (.mul (.c (32)) (.mul (.pow psi6E 3) x10E)) (.mul (.c (-2736)) (.mul psi6E (.mul x10E x12E))))))

def dK7 : ℤ := 5184

def data7 : Data := ⟨blocksPE, 7, dK7, rhsE7⟩

/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = 7, over every commutative ring. -/
theorem gen7_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data7.gen s0 s1 s2 s3 = 0 :=
  data7.gen_eq_zero (2 ^ 71) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3

/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = 8. -/
def rhsE8 : PE := (.add (.add (.mul (.c (8)) (.mul (.pow psi4E 3) (.pow x10E 2))) (.mul (.c (3)) (.mul (.pow psi4E 2) (.pow x12E 2)))) (.add (.mul (.c (-48)) (.mul psi4E (.mul psi6E (.mul x10E x12E)))) (.add (.mul (.c (160)) (.mul (.pow psi6E 2) (.pow x10E 2))) (.mul (.c (-4752)) (.mul (.pow x10E 2) x12E)))))

def dK8 : ℤ := 1728

def data8 : Data := ⟨blocksPE, 8, dK8, rhsE8⟩

/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = 8, over every commutative ring. -/
theorem gen8_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data8.gen s0 s1 s2 s3 = 0 :=
  data8.gen_eq_zero (2 ^ 74) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3

/-- integer form of `P_k`: `D_k · P_k(Ψ₄/4, Ψ₆/4, -X₁₀/2¹⁴, X₁₂/(2¹⁷·3))`, k = 9. -/
def rhsE9 : PE := (.add (.mul (.c (-30)) (.mul psi4E (.mul (.pow x10E 2) x12E))) (.add (.mul (.c (112)) (.mul psi6E (.pow x10E 3))) (.mul (.c (1)) (.pow x12E 3))))

def dK9 : ℤ := 216

def data9 : Data := ⟨blocksPE, 9, dK9, rhsE9⟩

/-- The identity `D_k e_k = Σ n Ψ₄^i Ψ₆^j X₁₀^l X₁₂^m` in `s`, k = 9, over every commutative ring. -/
theorem gen9_eq_zero {R : Type*} [CommRing R] (s0 s1 s2 s3 : R) : data9.gen s0 s1 s2 s3 = 0 :=
  data9.gen_eq_zero (2 ^ 75) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) s0 s1 s2 s3

end IgusaAlgEval
