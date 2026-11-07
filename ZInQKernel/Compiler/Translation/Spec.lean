import ZInQKernel.Compiler.Translation.WellFormed
import ZInQKernel.Compiler.Translation.RecipeRelation
import ZInQKernel.Model.Generator
import ZInQKernel.Compiler.Translation.Points

/-!
# The shape of a translated recipe

The model-evaluation translation of a natural circuit `𝒩` (syntax chapter) produces a
model-evaluation recipe `ρ` by one allocation counter. The semantic statements of this chapter
use only the following facts about its output, collected in `TranslationShape`:

* every explicit variable `v` has a point reference `vref v` (`5i` for the input `i`) and a
  source row `(vref v, s)` with a natural start `s` unless `v` is an input and the inputs are
  unconstrained;
* every node `j` has a point reference `pt j`: the reference of `i` for `var i`, `-1, -2, -3` for
  the constants `0, 1, -1`, the point of a constant definition by the fixed-scalar template
  `S_c` for any other constant `c`, and the output point of an operation
  `(0, pt a, pt b, pt j)`, `(1, pt a, pt b, pt j)` or `(2, pt a, pt b, pt c, pt j)` for an
  addition, multiplication or call node;
* the root equality is `(pt root, 5k)` in value mode and `(pt root, -1)` in zero mode;
* conversely every natural row, constant definition and operation of `ρ` comes from an explicit
  variable or a node in this way;
* the fresh points (inputs, output, explicit witnesses, nodes with a fresh point) are pairwise
  disjoint blocks of five variables unless they are one allocation (all occurrences of a
  constant share one point), and avoid the generator variables.

Also defined here: the property (PV) of a power recipe and the semantic hypotheses on the callee
templates.
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

/-! ### The power-value property -/

/-- The assignment `(a, b, c, w₀, …, w_{V_𝒫 - 4}, 0, 0, …)` of the power template. -/
def blockAssign (P : NatCircuit) (a b c : ℤ) (w : Fin (P.varCount - 3) → ℕ) (i : ℕ) : ℤ :=
  if i < 3 then [a, b, c].getD i 0 else if h : i - 3 < P.varCount - 3 then (w ⟨i - 3, h⟩ : ℤ) else 0

/-- **(PV)**: on three canonical input codes the power recipe `π` relates exactly the codes of
the values of the power template at those integers and natural witnesses:
`Rel_π(ι(a), ι(b), ι(c), r) ⟺ ∃ w ∈ ℕ^{V_𝒫 - 3}, r = ι(T_𝒫(a, b, c, w))`. -/
def PowerValueSpec (π : ExPoly) (P : NatCircuit) : Prop :=
  ∀ (a b c : ℤ) (r : Fin 5 → ℚ), CodeRel π [iota a, iota b, iota c, r] ↔
    ∃ w : Fin (P.varCount - 3) → ℕ, r = iota (templateValue P (blockAssign P a b c w))

/-! ### Semantic hypotheses on the callees -/

/-- The callee semantics used by the translation: the natural-code predicate (`ν`), raw addition
on canonical codes (`α`), multiplication on canonical codes (`μ`) and the fixed-scalar templates
`S_c`, `c ≥ 2`, at `ι(1)` (`scalarOf`). -/
structure CalleeSemantics (ν α μ : ExPoly) (scalarOf : ℤ → ExPoly) : Prop where
  natural : ∀ A, CodeRel ν [A] ↔ ∃ n : ℕ, A = iota n
  add : ∀ (a b : ℤ) (R : Fin 5 → ℚ), CodeRel α [iota a, iota b, R] ↔ R = iota (a + b)
  mul : ∀ (a b : ℤ) (R : Fin 5 → ℚ), CodeRel μ [iota a, iota b, R] ↔ R = iota (a * b)
  scalar : ∀ c : ℤ, 2 ≤ c → ∀ R : Fin 5 → ℚ, CodeRel (scalarOf c) [iota 1, R] ↔ R = iota c

/-! ### The shape of the translation -/

/-- The value-determining identity of a fresh point: an explicit variable (inputs included), the
output, a node, or a nontrivial constant (shared by all its occurrences). -/
inductive Slot
  | var (i : ℕ)
  | out
  | node (j : ℕ)
  | const (c : ℤ)
  deriving DecidableEq

/-- `c` is a nontrivial constant (not `0`, `1` or `-1`). -/
def Nontrivial (c : ℤ) : Prop := c ≠ 0 ∧ c ≠ 1 ∧ c ≠ -1

/-- The facts about a recipe `ρ` translated from `𝒩` (power template `𝒫`) in value mode
(`value = true`) or zero mode, with (`natIn = true`) or without natural constraints on the
inputs; `scalarOf c` is the fixed-scalar template of the constant `c`. -/
structure TranslationShape (templates recipes : List ExPoly) (scalarOf : ℤ → ExPoly)
    (r : ModelRecipe) (P N : NatCircuit) (value natIn : Bool) where
  /-- The point reference of the explicit variable with index `i`. -/
  vref : ℕ → ℤ
  /-- The point reference of node `j`. -/
  pt : ℕ → ℤ
  /-- The parameters are the input codes and, in value mode, the output code. -/
  params : r.parameterCount = 5 * (N.inputCount + if value then 1 else 0)
  /-- The input `i` is the parameter point `5i`. -/
  vref_input : ∀ i < N.inputCount, vref i = 5 * i
  /-- Natural rows: every explicit variable except an unconstrained input. -/
  row : ∀ v ∈ N.explicitVars, (natIn = true ∨ v.2 = VarKind.witness) →
    ∃ s, (vref v.1, some s) ∈ r.sources
  /-- Every natural row comes from an explicit variable. -/
  row_inv : ∀ row ∈ r.sources, ∀ s, row.2 = some s →
    ∃ v ∈ N.explicitVars, row.1 = vref v.1 ∧ (natIn = true ∨ v.2 = VarKind.witness)
  /-- A variable node points at its variable. -/
  pt_var : ∀ j (hj : j < N.nodes.length) i, N.nodes[j] = .var i → pt j = vref i
  /-- The constant `0` is the reference `-1`. -/
  pt_zero : ∀ j (hj : j < N.nodes.length), N.nodes[j] = .const 0 → pt j = -1
  /-- The constant `1` is the reference `-2`. -/
  pt_one : ∀ j (hj : j < N.nodes.length), N.nodes[j] = .const 1 → pt j = -2
  /-- The constant `-1` is the reference `-3`. -/
  pt_neg_one : ∀ j (hj : j < N.nodes.length), N.nodes[j] = .const (-1) → pt j = -3
  /-- A nontrivial constant is the point of a constant definition by `S_c`. -/
  pt_const : ∀ j (hj : j < N.nodes.length) c, N.nodes[j] = .const c → Nontrivial c →
    ∃ d ∈ r.constants, d.2.1 = pt j ∧ getEx templates d.1 = scalarOf c
  /-- Every constant definition comes from a nontrivial constant node. -/
  const_inv : ∀ d ∈ r.constants, ∃ j, ∃ (hj : j < N.nodes.length), ∃ c,
    N.nodes[j] = .const c ∧ Nontrivial c ∧ d.2.1 = pt j ∧ getEx templates d.1 = scalarOf c
  /-- An addition node is the output of a raw addition. -/
  op_add : ∀ j (hj : j < N.nodes.length) a b, N.nodes[j] = .add a b →
    ∃ s, Operation.add (pt a) (pt b) (pt j) s ∈ r.operations
  /-- A multiplication node is the output of a multiplication. -/
  op_mul : ∀ j (hj : j < N.nodes.length) a b, N.nodes[j] = .mul a b →
    ∃ s, Operation.mul (pt a) (pt b) (pt j) s ∈ r.operations
  /-- A call node is the output of a power call. -/
  op_call : ∀ j (hj : j < N.nodes.length) a b c w, N.nodes[j] = .call a b c w →
    ∃ s, Operation.power (pt a) (pt b) (pt c) (pt j) s ∈ r.operations
  /-- Every operation comes from a node. -/
  op_inv : ∀ op ∈ r.operations, ∃ j, ∃ (hj : j < N.nodes.length),
    (∃ a b s, N.nodes[j] = .add a b ∧ op = .add (pt a) (pt b) (pt j) s) ∨
    (∃ a b s, N.nodes[j] = .mul a b ∧ op = .mul (pt a) (pt b) (pt j) s) ∨
    (∃ a b c w s, N.nodes[j] = .call a b c w ∧ op = .power (pt a) (pt b) (pt c) (pt j) s)
  /-- The root equality. -/
  root : r.rootEq = (pt N.root, if value then 5 * (N.inputCount : ℤ) else -1)
  /-- A power recipe is present when there are call nodes. -/
  power : HasCall N → r.power.isSome
  /-- The three generator variables are distinct. -/
  gen_distinct : r.generator 0 ≠ r.generator 1 ∧ r.generator 0 ≠ r.generator 2 ∧
    r.generator 1 ≠ r.generator 2
  /-- The fresh points with their identities. -/
  slots : List (ℕ × Slot)
  /-- Distinct fresh points are disjoint blocks of five variables. -/
  slots_sep : slots.Pairwise fun e e' => e = e' ∨ Separated e.1 e'.1
  /-- The fresh points avoid the generator variables. -/
  slots_gen : ∀ e ∈ slots, ∀ m : Fin 3, ¬ (e.1 ≤ r.generator m ∧ r.generator m < e.1 + 5)
  /-- The inputs are fresh points. -/
  slot_input : ∀ i < N.inputCount, (5 * i, Slot.var i) ∈ slots
  /-- In value mode, the output is a fresh point. -/
  slot_out : value = true → (5 * N.inputCount, Slot.out) ∈ slots
  /-- The explicit witnesses are fresh points. -/
  slot_var : ∀ v ∈ N.explicitVars, v.2 = VarKind.witness → ∃ q : ℕ, vref v.1 = q ∧ (q, Slot.var v.1) ∈ slots
  /-- Additions, multiplications and calls are fresh points. -/
  slot_node : ∀ j (hj : j < N.nodes.length), (∀ i, N.nodes[j] ≠ .var i) →
    (∀ c, N.nodes[j] ≠ .const c) → ∃ q : ℕ, pt j = q ∧ (q, Slot.node j) ∈ slots
  /-- A nontrivial constant is a fresh point shared by its occurrences. -/
  slot_const : ∀ j (hj : j < N.nodes.length) c, N.nodes[j] = .const c → Nontrivial c →
    ∃ q : ℕ, pt j = q ∧ (q, Slot.const c) ∈ slots

end ZInQ.Translation
