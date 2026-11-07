# assembly-top: report

Top of the assembly chapter and the main theorem. Code is in `ZInQKernel/Assembly/Top/`
(namespace `ZInQ.Assembly`), root module `ZInQKernel/Assembly/Top.lean` (imported from
`ZInQKernel.lean`), and in `ZInQKernel/Main.lean`. `lake build ZInQKernel` succeeds;
`scripts/check_target.py` passes. No `sorry`, `axiom` or `native_decide`.

`#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck` gives
`[propext, Classical.choice, Quot.sound]`; the same holds for `main_branch_eq`, `value_relation_iff`
and `Pstar_spec`. Both merges happened (origin/wip/assembly-close and origin/wip/mult-top; also
origin/wip/nat-programs), so `sorryAx` does not appear.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| assembly/main-branch-exactness.md | `ZInQ.Assembly.main_branch_eq` (`Top/ValueRelation.lean`); core: `eq_of_close_of_test`, `ratHeight_le_bound_of_test` (`Top/MainBranch.lean`) | proved |
| assembly/ordinary-value-relation.md | `ZInQ.Assembly.value_relation_iff`, `ZInQ.Assembly.exists_value_relation_iff` (`Top/ValueRelation.lean`) | proved |
| assembly/assembly-lemma.md | `ZInQ.Assembly.Pstar_spec`, `ZInQ.Assembly.assembly` (`Top/Assembly.lean`) | proved (with `HaltingNodeCheck` as a hypothesis, see below) |
| main/main-theorem.md | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck` (`Main.lean`) | proved (with `HaltingNodeCheck`) |

`ZInQ.exists_bounded_integer_polynomial_defining_integers_of`, the theorem with four hypotheses,
still ends in `sorry`, as the task specified. Once `HaltingNodeCheck` has a kernel proof
`h`, its proof is `exists_bounded_integer_polynomial_defining_integers_of_nodeCheck h hH hPC h22 hCAT`.

Also done: `Compiler.natural_polynomial_semantics` (`Compiler/Universal/WrapperCode.lean`) is
now `natural_polynomial_semantics_of interpreter_accepts_iff IR.wrapper_halts_encode c`, after
merging nat-programs. This was a one-line change. The docstring above it still says that the
proof waits for wrapper correctness; the owner of the file should update it.

## Statements

`CloseRel N K t := ValRel (getEx closeSpecLib 2) (List.ofFn N ++ (List.ofFn K ++ [t]))` and
`ValueRel N t := ValRel (getEx closeSpecLib 5) (List.ofFn N ++ [t])` (`Top/Spec.lean`).
`closeSpecLib` (from assembly-close) is `specLib specConstructors cstar ell T (c3 : ℤ)
(precisionCircuitOf c3)`, the library of `specPstar (c3 : ℤ)`.

```lean
theorem main_branch_eq (hH) (hPC) (h22) {n κ : ℤ} {t : ℚ}
    (hc : CloseRel (iota n) (iota κ) t) (hT : Test n κ t) : t = n
theorem value_relation_iff (hH) (hPC) (h22) (N : Fin 5 → ℚ) (t : ℚ) :
    ValueRel N t ↔ ∃ n : ℤ, N = iota n ∧ t = n
theorem exists_value_relation_iff (hH) (hPC) (h22) (t : ℚ) :
    (∃ N : Fin 5 → ℚ, ValueRel N t) ↔ ∃ z : ℤ, (z : ℚ) = t
theorem Pstar_spec (hN : HaltingNodeCheck) (hH) (hPC) (h22) (hCAT) :
    (specPstar (c3 : ℤ)).totalDegree < hyperoperation 4 2 7 ∧
    (∀ m, ((specPstar (c3 : ℤ)).coeff m).natAbs < hyperoperation 4 2 8) ∧
    ∀ q : ℚ, (∃ w, MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (specPstar (c3 : ℤ)) = 0) ↔
      ∃ z : ℤ, (z : ℚ) = q
theorem assembly (hN) (hH) (hPC) (h22) (hCAT) : FrozenTarget
```

## Statement corrections

- assembly-lemma and main-theorem: the article assumes only H, PC, 22P and CAT. In Lean, the
  zero projection (`specPstar_zero_projection`) and the size bounds (`Pstar_target_bounds`) both
  use the shape of the natural precision circuit, which depends on the named finite check
  `Compiler.Universal.HaltingNodeCheck`. So `Pstar_spec`, `assembly` and the main theorem take
  `hN : HaltingNodeCheck` as an extra explicit hypothesis. It is a finite-computation input of
  milestone 1, not a mathematical change.
- ordinary-value-relation: the implementation note's names `value_rel_iff`/`exists_value_rel_iff`
  clash with the generic composition lemma `ZInQ.Assembly.value_rel_iff`
  (`Assembly/Values/Outer.lean`). The leaves are therefore `value_relation_iff` and
  `exists_value_relation_iff`, following assembly-close's `close_relation_iff`.
- main-branch-exactness: the statement is as in the article. The proof needs `n ∉ 𝒞`, which comes
  from soundness of Close, not from the tests: if `κ F(n) = 0`, the divisibility `M ∣ κF(n)`
  carries no information. The core lemma `eq_of_close_of_test` therefore takes `n ∉ 𝒞` explicitly.
- The assembly lemma does not take MW: it is the theorem `mordellWeilE`, used through
  `iota_injective` and membership.

## Lemmas added beyond the leaves (namespace `ZInQ.Assembly`)

- `Top/MainBranch.lean`:
  - `ratHeight_eq_rationalLogHeight`: bridge to the upstream helper, by `rfl`.
  - `ratHeight_le_bound_of_test`: `h(t) ≤ 𝓑(n, κ)`, from `test_dvd`, `Nat.le_of_dvd` and
    `sixContact_at_heightPrimes`.
  - `eq_of_close_of_test`: via upstream `eq_int_of_real_abs_sub_lt_exp_neg_of_height_le`.
- `Top/Spec.lean`: `CloseRel`, `ValueRel`, `SpecMultiplicationExact`.
- `Top/ValueRelation.lean`: `main_branch_eq_of`, `value_relation_iff_of` and
  `exists_value_relation_iff_of`, which take soundness and completeness of Close as hypotheses
  (in the exact form of `close_sound`/`close_complete`) and M as `hM`.
- `Top/Assembly.lean`:
  - `c3_natAbs_lt`: `|c₃| < 2^(2^24)`, from `c3_lt'` without simp.
  - `specPstar_zero_projection_valueRel`: the zero projection in terms of `ValueRel`.
  - `Pstar_spec_of`.

No large constant is evaluated anywhere. `A0` and `bound` are handled through `bound`'s equation
and `Nat.cast_*`.

## Problems

None. Every leaf compiled on its first build.

## Suggestions for the next agent

- When `HaltingNodeCheck` gets a kernel certificate, replace the `sorry` in
  `exists_bounded_integer_polynomial_defining_integers_of` by
  `exists_bounded_integer_polynomial_defining_integers_of_nodeCheck <proof> hH hPC h22 hCAT` and
  update `main/main-theorem.md`.
- Blueprint `lean:` fields: main-branch-exactness → `ZInQ.Assembly.main_branch_eq`;
  ordinary-value-relation → `ZInQ.Assembly.value_relation_iff, ZInQ.Assembly.exists_value_relation_iff`;
  assembly-lemma → `ZInQ.Assembly.Pstar_spec, ZInQ.Assembly.assembly`.
