# dprm-scout

**Result.** The integer-H10 premise `hZ : ¬ ComputablePred ZInQ.Contrib.H10Reduction.IntCodeSolvable` of
`ZInQ.OneProof.rationalH10` is proved from one printed leaf, the DPRM theorem for subsets of ℕ, with all glue
proved in Lean. File `ZInQKernel/Contrib/OneProof/IntegerH10.lean` (namespace `ZInQ.Contrib.IntegerH10`,
imports only `ZInQKernel.Contrib.H10Reduction` and Mathlib):

* leaf `DPRMNat : ∀ p : ℕ → Prop, REPred p → ∃ n (Q : MvPolynomial (Fin (n+1)) ℤ), ∀ x, p x ↔ ∃ y : Fin n → ℕ,
  Q(x, y) = 0` — printed form (Matiyasevich 1970; Davis, Amer. Math. Monthly 80 (1973), "every r.e. set is
  Diophantine"), case n = 1; gaps (arity, ℕ vs positive integers, r.e. definition) all in the weakening
  direction; flag "unread" (no print on host, locators UNVERIFIED);
* `not_computable_intCodeSolvable_of_dprm : DPRMNat → ¬ ComputablePred IntCodeSolvable`;
* `rational_not_computable_of_frozenTarget_dprm : FrozenTarget → DPRMNat → ¬ ComputablePred RatCodeSolvable`;
* `DPRMDioph` (same leaf over Mathlib's `Dioph`) and `dprmNat_of_dprmDioph`.

Glue: halting set on ℕ (Mathlib `halting_problem_re`/`halting_problem`), four squares
(`Nat.sum_four_squares`), many-one reduction `x ↦ (4n+1, encode (c₀ ++ tailCode x))` decoding to
`Q₄² + (X₀ − x)²` with #150's `code_complete`. No hypothesis on #150's coding is needed.

**Compiles.** `lake build ZInQKernel.Contrib.OneProof.IntegerH10` succeeds, no warnings; axioms of all four
theorems: propext, Classical.choice, Quot.sound. `#discharges`: see docs/research/dprm-scout.md
(hZ is not a `frozenTarget` hypothesis, so it matches nothing there; autofold.py does not apply;
scratch/dprm-scout/autofold.json records the intended one-line change of `rationalH10`).

**Remains.** DPRM itself (road map in docs/research/dprm-scout.md: Route A over Mathlib's `Nat.Primrec` and
`Code.evaln` — exponentiation is in Mathlib (`Dioph.pow_dioph`); binomial, factorial, the bounded universal
quantifier (Davis–Putnam–Robinson 1961) and Primrec-graph glue are open; Route B register machines as in the
Isabelle/Coq formalizations). Integration note: after merging origin/main, `RationalH10.lean` still passes
`OpenResearchLeaves38/OpenTextbookLeaves16` to a `frozenTarget` that now takes `…40/…17`; it needs its binder
types updated (not edited: outside scope).
