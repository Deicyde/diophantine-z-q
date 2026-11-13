import ZInQKernel.Compiler.Interpreter.Encode
import ZInQKernel.Compiler.Universal.Halting

/-!
# Size of a program literal

A primitive program `p` is *small* if `3 ≤ m ≤ 200,000` (`m` its length) and every register
index and target of its instructions is below `2^18`. For a small valid program,

  `1399 < code(p) < 2^14400019 < 2^(2^24)`.

The value of `code(p)` is never computed: the width is at most `18` (`width_spec`), so
`code(p) < 2^(18(4m + 1) + 1) ≤ 2^14400019` (`code_lt`), and `code(p) + 1 ≥ 2^(w(4m - 7) + 1) ≥
2^11` (`code_ge`). The size check of the wrapper (`wrapper-size-check.md`) is the statement that
the wrapper is small; the size of the program literal `c₃` (`wrapper-code-size.md`) is the
instance of these bounds.

The semantics of the universal halting circuit (`halting-polynomial-semantics.md`) is also
stated here, since it needs the program numbering.
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open RM Natural

/-- A small program: `3 ≤ m ≤ 200,000` and every register index and target below `2^18`. -/
def SmallProgram (p : Program) : Prop :=
  3 ≤ p.length ∧ p.length ≤ 200000 ∧ ∀ ins ∈ p, instrMaxField ins < 2 ^ 18

theorem maxField_lt_of_forall {p : Program} {B : ℕ} (hB : 0 < B)
    (h : ∀ ins ∈ p, instrMaxField ins < B) : maxField p < B := by
  unfold maxField
  induction p with
  | nil => simpa using hB
  | cons a p ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_lt (h a List.mem_cons_self) (ih fun ins hins => h ins (List.mem_cons_of_mem _ hins))

theorem width_le_of_small {p : Program} (h : SmallProgram p) : width p ≤ 18 :=
  (width_spec p).2.2 18 (by norm_num) (maxField_lt_of_forall (by norm_num) h.2.2)

/-- **The program literal of a small program is below `2^14400019`.** -/
theorem code_lt_of_small {p : Program} (h : SmallProgram p) : code p < 2 ^ 14400019 := by
  have hw := width_le_of_small h
  refine lt_of_lt_of_le (code_lt p) (pow_le_pow_right₀ (by norm_num) ?_)
  have : width p * (4 * p.length + 1) ≤ 18 * (4 * 200000 + 1) :=
    Nat.mul_le_mul hw (by have := h.2.1; omega)
  omega

theorem two_pow_14400019_lt : (2 : ℕ) ^ 14400019 < 2 ^ 2 ^ 24 :=
  pow_lt_pow_right₀ (by norm_num) (by norm_num)

/-- **The program literal of a small valid program exceeds `1399`.** -/
theorem code_gt_of_small {p : Program} {r : ℕ} (hp : p.Valid r) (h : SmallProgram p) :
    1399 < code p := by
  have h1 := code_ge p r hp (by have := h.1; omega)
  have h2 : 2 ^ 11 ≤ 2 ^ (width p * (4 * p.length - 7) + 1) := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    have hw := (width_spec p).1
    have : 2 * 5 ≤ width p * (4 * p.length - 7) :=
      Nat.mul_le_mul hw (by have := h.1; omega)
    omega
  have : (2 : ℕ) ^ 11 = 2048 := by norm_num
  omega

/-! ### Semantics of the universal halting circuit -/

/-- The universal halting circuit has a natural zero at `(e, n)` iff `𝒰` accepts `(e, n)`;
with the correctness of the interpreter this is `halts(e, n)`. -/
theorem haltingCircuit_natRel_iff_of
    (hU : ∀ e n, interpreter.Accepts ![e, n] ↔ halts e n) (e n : ℕ) :
    haltingCircuit.NatRel powerTemplate ![e, n] ↔ halts e n :=
  (haltingCircuit_natRel_iff_accepts e n).trans (hU e n)

end ZInQ.Compiler.Universal
