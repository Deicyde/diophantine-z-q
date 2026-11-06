# bp-compiler-translation: report

Chapter: `blueprint/roadmap/compiler/` (container README), `compiler/translation/` (Section 10.4)
and its subchapter `compiler/translation/machine/` (Section 10.3). Locators:
`blueprint/sources/compiler-translation-locators.md`. One implementation note per leaf under
`blueprint/.implementation-notes/`. `autoform check` is OK; `autoform audit` reports no finding
in my paths (the remaining errors are the coverage rows and the other chapters' stubs).

## Articles written

Containers: `compiler/README.md`, `compiler/translation/README.md`,
`compiler/translation/machine/README.md`.

`compiler/translation/` (12 leaves):

| File | Kind | Content |
| --- | --- | --- |
| lagrange-four-squares | theorem, background | Lagrange (Mathlib `Nat.sum_four_squares`) |
| natural-code-semantics | theorem, cited | `Rel_natural(A) ⇔ A = ι(n), n ∈ ℕ`, all-input, from M (all-input) + MW |
| natural-circuit-values | def, bridged | node values, polynomial `[[N]]`, admissible assignments; `C = [[N]]` |
| natural-circuit-well-formed | def, bridged | scope conditions W1-W7 |
| model-recipe-relation | theorem, bridged | `Rel_ρ` unfolds into callee relations on point references |
| translation-soundness | theorem, cited | every node point is `ι(value)` (source-DAG induction) |
| translation-completeness | theorem, cited | natural solutions give rational witnesses |
| model-evaluation-semantics | theorem, cited | the two-mode generic translation theorem |
| precision-circuit-scope | theorem, cited | FINITE CHECK: power template and precision circuit are well-formed |
| power-value-semantics | theorem, cited | `Rel_pv(ι a, ι b, ι c, r) ⇔ ∃ w ∈ ℕ⁷⁹, r = ι(T(a,b,c,w))` |
| rational-translation (interface) | theorem, cited | `Rel_precision(E) ⇔ ∃ c ∈ ℕ⁵, E_i = ι(c_i) ∧ ∃ z ∈ ℕ¹³⁰⁵⁸⁰⁶, C(c,z) = 0`, plus power_value |
| precision-decision | theorem, bridged | composite with (C.4): `Rel_precision(E) ⇔ E = ι(c) ∧ accepts_naturals(c)` |

`compiler/translation/machine/` (23 leaves): register-programs (def), program-numbering (def),
program-numbering-decode (lemma), list-codes (lemma), structured-programs (def), lowering (def),
lowering-correctness (theorem), universal-interpreter (def), interpreter-step (lemma),
interpreter-correctness (theorem), precision-predicate (def), nondegenerate-multiples (lemma),
quadratic-norm-zero (lemma), capped-arithmetic (lemma), jacobian-formulas (lemma), precision-ir
(def), ir-correctness (theorem), cantor-unpairing (lemma), wrapper (def, defines `c_3`),
wrapper-correctness (theorem), precision-machine-semantics (theorem:
`U accepts (c_3, encode5 c) ⇔ accepts_naturals c`), five-input-specialization (def, generic
`Spec(H, e₀)`), specialization-semantics (theorem, generic in `H`, `e₀`).

## Finite computations

Only one leaf is a finite check: **precision-circuit-scope**.
- (1) The power template (474 nodes, 82 variables): explicit variables `0..81`, no calls, var
  nodes in range, operands earlier, constants `4, 2, 3`. Kernel `decide` on the concrete term.
- (2) The precision circuit (293,620 nodes, 54,056 explicit variables, 15,845 blocks of 79):
  inputs first, distinct indices, var nodes explicit, operands earlier, blocks pairwise
  disjoint and disjoint from explicit variables, everything below 1,305,811, constants
  `c_3, 2, 4, 1399`. Method: preferably by construction from the natural chapter's compiler
  and the specialization (shift by 7); fallback a sound Boolean checker run with
  `native_decide` (milestone 1). The checker must not force `c_3`; `c_3 ≥ 2` is proved from its
  definition (`code_ge_five`), never by evaluation.
- Optional cross-check (universal-interpreter note): `universalInterpreter.length = 1399`,
  204 registers, by `decide`.

## Extra hypotheses

None beyond the five. The translation theorems take MW and the multiplication statement M (in
its all-input form) as explicit hypotheses (`hMW`, `hM : MultiplicationExact`); M comes from
the multiplication chapter under the five hypotheses. The machine subchapter uses none (it is
MW-free; nondegenerate-multiples uses only the torsion theorem).

## Manuscript issues and expansions

1. *Reproducibility of the natural polynomial.* The sources S21 (`variable-shift-precision.py`),
   S22 (`precision-register.js`), S23 (`specialize-precision.js`) and the universal interpreter
   generator are not in the repository (Appendix B lists them; only the archive has them). The
   witness counts of the syntax chapter (54,051 explicit witnesses, 15,845 power calls, hence
   292,890,231,904 witnesses in all, exactly the budget) depend on the exact 1,399-state,
   204-register interpreter `U`. The Lean construction must reproduce `U` exactly (restore the
   archived generator) or recompute the counts and stay within budget; a direct compilation of
   the precision machine without the universal interpreter would exceed the budget by orders of
   magnitude. The precision program and its lowering affect only the constant `c_3`; written
   afresh in Lean they give a different `c_3`, so the external byte-level cross-check of
   `precision-natural-polynomial.json` will differ in node 0 (no effect on the proof).
2. *The predicate needs nondegeneracy.* "For nonzero multiples of `P_0`, `z = -x/y` is
   well-defined" presupposes that `P_0` has infinite order. To keep the predicate total and the
   compiler MW-free, condition 2 of precision-predicate adds explicit degenerate rejections,
   and nondegenerate-multiples shows they never fire (torsion theorem, no Mordell-Weil).
3. *`A_ht^(0) = H_6(S_ht)`* uses the convention of line 399, `R = max(D, 324, 10^12) = D`, so
   `A_ht^(0) = 2·10^13·max(1, C_cm, D^{17 D E_0})`; stated explicitly.
4. *Natural predicate.* The manuscript's sketch leaves implicit that the two index witnesses
   of `multiply(σ_i, σ_i, Σ_i)` coincide; the proof uses injectivity of `ι` (generator
   certificate, MW). Likewise "root equality ⇒ value 0" in zero mode uses injectivity. So the
   rational translation (unlike (C.4)) does depend on the rational model.
5. *Positivity of constants.* The fixed-scalar semantics needs `val ≥ 1`; the circuits' nontrivial
   constants are positive (`c_3 ≥ 2` from its definition), which the manuscript does not state
   (the translator rejects nonpositive constants). Recorded as well-formedness condition 4.
6. *Jacobian formulas.* S22's exact formulas are unavailable; jacobian-formulas states the
   standard Jacobian doubling/addition on `Y² = X³ + AXZ⁴` with the manuscript's case splits;
   the manuscript's "nine identities" cannot be matched one to one.
7. *Order of use.* 10.4 says "Apply (C.4) using the exact signed index model"; the rational
   translation is in fact independent of (C.4), which is needed only for the decision
   corollary (precision-decision).

## Coordination points / open questions

- **natural/ chapter (parallel).** Overlap with Section 10 opening and 10.1: I defined the
  precision predicate (`machine/precision-predicate.md`), primitive register programs and
  their acceptance (`machine/register-programs.md`), capped arithmetic, Cantor unpairing and the
  generic specialization `Spec(H, e₀)`. The natural chapter should (a) use these definitions
  (or the lead merges duplicates), (b) define the natural precision polynomial as
  `Spec(H_univ, c_3)` with `c_3` from `machine/wrapper.md`, and (c) prove (C.4) in
  `natural-polynomial-semantics.md` from: its packed-compiler theorem for `U`
  (`∃v H(e,n,v)=0 ⇔ U accepts (e,n)`), `machine/specialization-semantics.md` and
  `machine/precision-machine-semantics.md`. These links are not in the graph yet because the
  interface article is theirs. No cycle arises as long as natural-polynomial-semantics does not
  become a statement dependency of a machine/ leaf (none of mine depends on it except
  precision-circuit-scope, rational-translation and precision-decision).
- **multiplication/ chapter.** My statements assume M in the all-input form
  `Rel_multiply(p,q,r) ⇔ ∃ a b, p = ι a ∧ q = ι b ∧ r = ι(ab)`; its interface article should
  state exactly this (a `MultiplicationExact : Prop` shared definition is suggested in the notes).
- **assembly/ chapter.** Use `precision-decision` (codes of signed encodings,
  `accepts_naturals`) rather than `C`.
- Push status: the commit is local; `git push` to GitHub failed (connection reset, proxy 403,
  SSH reset). Retried several times.
