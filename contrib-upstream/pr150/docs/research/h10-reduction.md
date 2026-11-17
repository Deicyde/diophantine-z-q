# Conditional H10 consumer on total integer-polynomial codes

`ZInQKernel/Contrib/H10Reduction.lean`, namespace
`ZInQ.Contrib.H10Reduction`, connects the original `ZInQ.FrozenTarget` to
computable many-one reducibility. It proves no arithmetic premise and assumes
integer-H10 noncomputability separately. It concerns the original target in
`ZInQKernel/Target.lean`, not the current manuscript's smaller quartic.

The compiler is ported from
[`the-omega-institute/trureturing`](https://github.com/the-omega-institute/trureturing),
commit `1441f3643dbae388fc0b90e134bb5677637045d0`, file
`D5/S0/Computability/Diophantine/IntegerToRational.lean`, SHA-256
`1ebedd8db9ffd537eb0b8ec85de75b88a8c8aa830a07b16a167d3bb68e222a9e`.
Its definitions and proof bodies are retained under the contribution namespace.
Both projects pin Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The original copyright and complete
Apache-2.0 licence are preserved in `ThirdParty/H10Reduction.LICENSE`; this
licence is scoped to this contribution and does not license the repository.
The licence is outside `Contrib/` because the existing kernel contract permits
only Lean sources there. The port and consumers were prepared by loning using
Codex CLI; kernel checks and external mathematical review have separate scope.

## Statements

Write `D(n,c) = decodePolynomial n (decodeCode c)`. Both predicates have type
`(ℕ × ℕ) → Prop` and use exactly this same integer-coefficient polynomial:

- `IntCodeSolvable (n,c)` is `∃ z : Fin n → ℤ, eval z (D(n,c)) = 0`.
- `RatCodeSolvable (n,c)` is
  `∃ x : Fin n → ℚ, eval₂ (Int.castRingHom ℚ) x (D(n,c)) = 0`.

The exported consumer types, with no additional section or instance premises,
are:

```lean
definesIntegers_of_frozenTarget :
  ZInQ.FrozenTarget →
  ∃ m : ℕ, ∃ P : MvPolynomial (Fin (m + 1)) ℤ, DefinesIntegers P

integer_manyOne_rational_of_frozenTarget :
  ZInQ.FrozenTarget → ManyOneReducible IntCodeSolvable RatCodeSolvable

integer_computable_of_rational_of_frozenTarget :
  ZInQ.FrozenTarget →
  ComputablePred RatCodeSolvable → ComputablePred IntCodeSolvable

rational_not_computable_of_frozenTarget :
  ZInQ.FrozenTarget →
  (¬ ComputablePred IntCodeSolvable) → ¬ ComputablePred RatCodeSolvable

rational_not_computable_of_canonicalInputs :
  ZInQ.SixContactMin →
  ZInQ.Literature.TYZThm35ReadingA →
  ZInQ.Literature.HeckeContinuation →
  ZInQ.Literature.FunctionalEquation5 →
  ZInQ.Literature.GrossZagier →
  (¬ ComputablePred IntCodeSolvable) → ¬ ComputablePred RatCodeSolvable
```

The first noncomputability theorem also accepts any alternative proof of the
same original `FrozenTarget`. The canonical corollary consumes exactly
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
in `ZInQKernel/MainLiterature.lean`, with its five unchanged inputs. Neither
route supplies `hZ : ¬ ComputablePred IntCodeSolvable`.

## Source, input and consumer correspondence

`DefinesIntegers P` requires the entire clause

```lean
∀ q : ℚ,
  (∃ w : Fin m → ℚ,
    eval₂ (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔
  ∃ z : ℤ, (z : ℚ) = q
```

`definesIntegers_of_frozenTarget` destructs the original target's witness and
retains precisely that polynomial and clause. Its `m` is inferred from their
actual types. At the present target, `m = 292890231904` and `m + 1 = 292890231905`;
the consumer maintains no duplicate dimension constant. The target's degree
and coefficient bounds remain part of the hypothesis but are not needed by
the reduction. No degree or coefficient bound on the output is asserted.

The remaining transitions are:

| Available result | Needed assertion and exact consuming construction |
|---|---|
| `code_complete`, exposed for raw codes by `effective_compiler.2.1` | For the *same* integer polynomial `P`, obtain a fixed natural `p` with `D(m+1,p) = P`. Rewriting by this equality supplies `DefinesIntegers (D(m+1,p))`. |
| `compileCodeNat_primrec`, exposed as `effective_compiler.1` | For fixed naturals `m,p`, compose with `(n,c) ↦ (n,m,p,c)`. This proves computability of `g(n,c) = compileCodeNat n m p c`, including its output dimension. |
| `decode_compileCode` and `solvability`, exposed as `effective_compiler.2.2` | For every `n,c`, rational solvability of `D(n*(m+1),(g(n,c)).2)` is equivalent to integer solvability of `D(n,c)`. Reverse this iff to obtain exactly `IntCodeSolvable a ↔ RatCodeSolvable (g a)`. |
| Mathlib `ManyOneReducible`, `Computability/Reduce.lean` | Package this *same* total `g`, its computability and the iff for all `a : ℕ × ℕ`; its first output component is definitionally `n*(m+1)`. |
| Mathlib `ComputablePred.computable_of_manyOneReducible` in the same file | Apply the proved reduction to `hQ : ComputablePred RatCodeSolvable`. The returned predicate is exactly `ComputablePred IntCodeSolvable`. |
| `integer_computable_of_rational_of_frozenTarget` | Apply the separate `hZ` to this returned proof, yielding `¬ ComputablePred RatCodeSolvable`. The canonical corollary first supplies the original target via the unchanged five-input theorem. |

The choices of `P`, `m` and `p` occur within a proof of a proposition asserting
existence of a computable map. Every fixed natural is a computable constant.
This does not define a computable extraction of `P` or `p` from an existential
proof, and does not assert one.

## Coverage and polynomial semantics

The port retains Mathlib's product/list `Primcodable` and `Encodable` instances.
A distributed term has a coefficient represented as a difference of naturals
and a word of variable indices. Repeated indices encode powers. Invalid
indices denote zero before multiplication; empty words denote one. A raw
natural that fails to decode denotes the empty term list and hence the zero
polynomial. The public predicates impose no validity filter.

The universal correctness and completeness proofs cover every `n : ℕ`,
including zero, all constants, zero, negative coefficients, malformed raw
codes, and words containing invalid indices. `renameCode` sends an invalid
input index to the out-of-range output index, preserving its zero semantics.
For each original variable `i`, `coordinate i j` is the row-major coordinate
`j + (m+1)*i`; `original i = coordinate i 0`. The product equivalence covers
all `n*(m+1)` output coordinates, also when `n = 0`.

The compiled integer polynomial is the square of the renamed input plus the
sum, over *all* `i : Fin n`, of squares of renamed copies of `P`. All are
evaluated at one joint rational assignment. `compile_zero_iff` uses the
ordered-field sum-of-squares theorem to recover every equation from that same
assignment. In the reverse direction, the integer assignment and one witness
block for each variable assemble through `finProdFinEquiv.symm` into that
single assignment. Rational casting of integer evaluation uses
`MvPolynomial.eval₂_comp` and the injectivity of the integer cast. These are
exact polynomial identities and quantified proofs, not finite-code sampling.

This contribution neither closes a registered arithmetic premise nor claims
integer DPRM, unconditional H10 over ℚ, or a new polynomial record. Compilation
and axiom checks establish formal facts about these explicit statements;
independent review and the repository's full integration and Protocol B
requirements remain distinct.
