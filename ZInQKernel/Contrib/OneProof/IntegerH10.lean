import ZInQKernel.Contrib.H10Reduction
import Mathlib.Computability.Halting
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.NumberTheory.Dioph

/-!
# Integer H10 for the coding of `H10Reduction`, from the DPRM theorem

`ZInQ.Contrib.H10Reduction.IntCodeSolvable` (upstream PR #150) is solvability over `ℤ` of the
integer polynomial decoded from a raw code `(n, c)`. This file proves
`¬ ComputablePred IntCodeSolvable` (the premise `hZ` of `ZInQ.OneProof.rationalH10`) from one
printed leaf, `DPRMNat`: every recursively enumerable set of natural numbers is Diophantine
(Matiyasevich 1970; Davis, Amer. Math. Monthly 80 (1973)), stated over Mathlib's `REPred` and
`MvPolynomial`. The glue (halting problem, four squares, the encoding into the raw codes) is proved.
-/

set_option autoImplicit false

namespace ZInQ.Contrib.IntegerH10

open MvPolynomial ZInQ.Contrib.H10Reduction

/-- **DPRM theorem** (Matiyasevich, Dokl. Akad. Nauk SSSR 191 (1970), building on Davis,
Putnam and Robinson, Ann. of Math. 74 (1961); exposition: M. Davis, "Hilbert's tenth problem is
unsolvable", Amer. Math. Monthly 80 (1973), 233–269, main theorem "every recursively enumerable
set is Diophantine"; page and display UNVERIFIED), the case of subsets of `ℕ`: for every
recursively enumerable predicate `p` on `ℕ` (Mathlib's `REPred`) there is a polynomial
`Q(x, y₁, …, yₙ)` with integer coefficients such that `p x` holds iff `Q(x, y) = 0` for some
natural numbers `y₁, …, yₙ`. (If the print counts from 1, positive integers, the statement for `ℕ`
follows by the substitution `x ↦ x + 1`, `yᵢ ↦ yᵢ + 1`.) -/
def DPRMNat : Prop :=
  ∀ p : ℕ → Prop, REPred p →
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℤ), ∀ x : ℕ,
      p x ↔ ∃ y : Fin n → ℕ, eval (fun i => ((Fin.cons x y : Fin (n + 1) → ℕ) i : ℤ)) Q = 0

/-! ## The halting set on `ℕ` -/

/-- Code `x` halts on input `0` (Mathlib's universal machine `Nat.Partrec.Code.eval`). -/
def haltSet (x : ℕ) : Prop :=
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code x) 0).Dom

theorem haltSet_re : REPred haltSet := by
  have h := ComputablePred.halting_problem_re 0
  unfold REPred at h ⊢
  exact h.comp (Computable.ofNat _)

theorem haltSet_not_computable : ¬ ComputablePred haltSet := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible
      ⟨Encodable.encode, Computable.encode, fun c => by
        simp only [haltSet, Denumerable.ofNat_encode]⟩ h)

/-! ## From natural to integer unknowns (Lagrange's four squares) -/

/-- Substitution: variable `0` stays, variable `i+1` becomes a sum of four squares. -/
noncomputable def sq4 (n : ℕ) : Fin (n + 1) → MvPolynomial (Fin (n * 4 + 1)) ℤ :=
  Fin.cons (X 0) (fun i => ∑ j : Fin 4, X (Fin.succ (finProdFinEquiv (i, j))) ^ 2)

theorem eval_bind₁_eq {n m : ℕ} (g : Fin n → MvPolynomial (Fin m) ℤ) (z : Fin m → ℤ)
    (Q : MvPolynomial (Fin n) ℤ) :
    eval z (bind₁ g Q) = eval (fun k => eval z (g k)) Q := by
  show eval₂Hom (RingHom.id ℤ) z (bind₁ g Q) = _
  rw [eval₂Hom_bind₁]
  rfl

theorem four_squares_iff {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℤ) (x : ℕ) :
    (∃ z : Fin (n * 4 + 1) → ℤ, z 0 = x ∧ eval z (bind₁ (sq4 n) Q) = 0) ↔
      ∃ y : Fin n → ℕ, eval (fun i => ((Fin.cons x y : Fin (n + 1) → ℕ) i : ℤ)) Q = 0 := by
  constructor
  · rintro ⟨z, hz0, hz⟩
    refine ⟨fun i => (∑ j : Fin 4, z (Fin.succ (finProdFinEquiv (i, j))) ^ 2).toNat, ?_⟩
    rw [eval_bind₁_eq] at hz
    refine Eq.trans (congrArg (fun w => eval w Q) ?_) hz
    funext k
    induction k using Fin.cases with
    | zero => simp [sq4, hz0]
    | succ i =>
      simp only [Fin.cons_succ, sq4, map_sum, map_pow, eval_X]
      rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  · rintro ⟨y, hy⟩
    choose a b c d h using fun i => Nat.sum_four_squares (y i)
    let w : Fin n × Fin 4 → ℕ := fun ij => ![a ij.1, b ij.1, c ij.1, d ij.1] ij.2
    let z : Fin (n * 4 + 1) → ℤ := Fin.cons (x : ℤ) (fun k => (w (finProdFinEquiv.symm k) : ℤ))
    have hz : ∀ i j, z (Fin.succ (finProdFinEquiv (i, j))) = (w (i, j) : ℤ) := fun i j => by
      simp only [z, Fin.cons_succ, Equiv.symm_apply_apply]
    refine ⟨z, by simp [z], ?_⟩
    rw [eval_bind₁_eq]
    refine Eq.trans (congrArg (fun w => eval w Q) ?_) hy
    funext k
    induction k using Fin.cases with
    | zero => simp [sq4, z]
    | succ i =>
      simp only [Fin.cons_succ, sq4, Fin.sum_univ_four, map_add, map_pow, eval_X]
      rw [hz i 0, hz i 1, hz i 2, hz i 3, ← h i]
      simp [w]

/-! ## Pinning variable `0` to the parameter -/

theorem decode_append' (n : ℕ) (a b : PolynomialCode) :
    decodePolynomial n (a ++ b) = decodePolynomial n a + decodePolynomial n b := by
  simp [decodePolynomial]

/-- The parameter-dependent tail: decodes to `-2x·X₀ + x²`. -/
def tailCode (x : ℕ) : PolynomialCode := [((0, 2 * x), [0]), ((x * x, 0), [])]

theorem eval_decode_tail (N : ℕ) (z : Fin (N + 1) → ℤ) (x : ℕ) :
    eval z (decodePolynomial (N + 1) (tailCode x)) = -2 * x * z 0 + (x : ℤ) * x := by
  simp [tailCode, decodePolynomial, codeVariable]
  try ring

theorem tailCode_primrec : Primrec tailCode := by
  unfold tailCode
  have h1 : Primrec (fun x : ℕ => (((0 : ℕ), 2 * x), [(0 : ℕ)])) :=
    ((Primrec.const 0).pair (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).pair
      (Primrec.const _)
  have h2 : Primrec (fun x : ℕ => ((x * x, (0 : ℕ)), ([] : List ℕ))) :=
    ((Primrec.nat_mul.comp Primrec.id Primrec.id).pair (Primrec.const 0)).pair
      (Primrec.const _)
  exact Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2 (Primrec.const []))

theorem decodeCode_encode' (c : PolynomialCode) : decodeCode (Encodable.encode c) = c := by
  simp [decodeCode]

/-- **Glue.** A predicate on `ℕ` given by a polynomial with natural unknowns many-one reduces to
`IntCodeSolvable`. -/
theorem manyOne_of_poly {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℤ) (p : ℕ → Prop)
    (hQ : ∀ x : ℕ,
      p x ↔ ∃ y : Fin n → ℕ, eval (fun i => ((Fin.cons x y : Fin (n + 1) → ℕ) i : ℤ)) Q = 0) :
    ManyOneReducible p IntCodeSolvable := by
  obtain ⟨c0, hc0⟩ := code_complete (n := n * 4 + 1) ((bind₁ (sq4 n) Q) ^ 2 + X 0 ^ 2)
  refine ⟨fun x => (n * 4 + 1, Encodable.encode (c0 ++ tailCode x)), ?_, fun x => ?_⟩
  · exact ((Primrec.const _).pair
      (Primrec.encode.comp (Primrec.list_append.comp (Primrec.const c0) tailCode_primrec))).to_comp
  · rw [hQ x, ← four_squares_iff]
    simp only [IntCodeSolvable, decodeCode_encode', decode_append', map_add, hc0, map_pow,
      eval_X, eval_decode_tail]
    constructor
    · rintro ⟨z, hz0, hz⟩
      exact ⟨z, by rw [hz, hz0]; ring⟩
    · rintro ⟨z, hz⟩
      have h1 : eval z (bind₁ (sq4 n) Q) ^ 2 + (z 0 - x) ^ 2 = 0 := by linear_combination hz
      have ha := sq_nonneg (eval z (bind₁ (sq4 n) Q))
      have hb := sq_nonneg (z 0 - (x : ℤ))
      have h2 : (z 0 - x) ^ 2 = 0 := by linarith
      have h3 : eval z (bind₁ (sq4 n) Q) ^ 2 = 0 := by linarith
      exact ⟨z, sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2),
        (pow_eq_zero_iff two_ne_zero).mp h3⟩

/-- **Integer H10 for `H10Reduction`'s coding, from DPRM.** No algorithm decides, from a raw code
`(n, c)`, whether the decoded integer polynomial has an integer zero. -/
theorem not_computable_intCodeSolvable_of_dprm (h : DPRMNat) :
    ¬ ComputablePred IntCodeSolvable := by
  obtain ⟨n, Q, hQ⟩ := h haltSet haltSet_re
  exact fun hc => haltSet_not_computable
    (ComputablePred.computable_of_manyOneReducible (manyOne_of_poly Q haltSet hQ) hc)

/-- **Rational H10 from `FrozenTarget` and DPRM** (upstream #150's consumer with `hZ` discharged). -/
theorem rational_not_computable_of_frozenTarget_dprm (h : ZInQ.FrozenTarget) (hD : DPRMNat) :
    ¬ ComputablePred RatCodeSolvable :=
  rational_not_computable_of_frozenTarget h (not_computable_intCodeSolvable_of_dprm hD)

/-! ## The same leaf over Mathlib's `Dioph`

`DPRMDioph` states DPRM with Mathlib's own `Dioph` (whose unknowns range over an arbitrary type);
it implies `DPRMNat`, so either form may serve as the leaf. -/

/-- **DPRM theorem**, Mathlib's `Dioph` form (same sources as `DPRMNat`): every recursively
enumerable predicate on `ℕ` is a Diophantine set of one-element vectors. -/
def DPRMDioph : Prop :=
  ∀ p : ℕ → Prop, REPred p → Dioph {v : Fin2 1 → ℕ | p (v Fin2.fz)}

theorem isPoly_eq_eval {α : Type} {f : (α → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ P : MvPolynomial α ℤ, ∀ v : α → ℕ, f v = eval (fun i => (v i : ℤ)) P := by
  induction hf with
  | proj i => exact ⟨X i, fun v => by simp⟩
  | const n => exact ⟨C n, fun v => by simp⟩
  | sub _ _ ihf ihg =>
    obtain ⟨P, hP⟩ := ihf
    obtain ⟨R, hR⟩ := ihg
    exact ⟨P - R, fun v => by simp [hP, hR]⟩
  | mul _ _ ihf ihg =>
    obtain ⟨P, hP⟩ := ihf
    obtain ⟨R, hR⟩ := ihg
    exact ⟨P * R, fun v => by simp [hP, hR]⟩

theorem dprmNat_of_dprmDioph (h : DPRMDioph) : DPRMNat := by
  intro p hp
  obtain ⟨β, q, hq⟩ := h p hp
  obtain ⟨P, hP⟩ := isPoly_eq_eval q.isPoly
  obtain ⟨n, f, hf, R, rfl⟩ := exists_fin_rename P
  let g : Fin n → Fin (n + 1) := fun i => Sum.elim (fun _ => 0) (fun _ => i.succ) (f i)
  refine ⟨n, rename g R, fun x => ?_⟩
  have hx := hq (fun _ => x)
  simp only [Set.mem_ofPred_eq] at hx
  rw [hx]
  simp only [hP, eval_rename]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i => Sum.elim (fun _ => x) t (f i), ?_⟩
    refine Eq.trans (congrArg (fun w => eval w R) ?_) ht
    funext i
    simp only [Function.comp_apply, g]
    rcases hfi : f i with a | b <;> simp [hfi]
  · rintro ⟨y, hy⟩
    refine ⟨Function.extend f y 0 ∘ Sum.inr, ?_⟩
    refine Eq.trans (congrArg (fun w => eval w R) ?_) hy
    funext i
    simp only [Function.comp_apply, g]
    rcases hfi : f i with a | b
    · simp
    · have he := hf.extend_apply y 0 i
      rw [hfi] at he
      simp [he]

/-- Integer H10 for `H10Reduction`'s coding from DPRM in Mathlib's `Dioph` form. -/
theorem not_computable_intCodeSolvable_of_dprmDioph (h : DPRMDioph) :
    ¬ ComputablePred IntCodeSolvable :=
  not_computable_intCodeSolvable_of_dprm (dprmNat_of_dprmDioph h)

end ZInQ.Contrib.IntegerH10
