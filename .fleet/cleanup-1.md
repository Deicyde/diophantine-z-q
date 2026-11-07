# cleanup-1 report

New modules: `ZInQKernel/Cleanup/{NonzeroMultiples,FixedPointCodes,GuardSemantics,ExplicitIdentities,Bridges,HierarchicalCalls}.lean`,
root `ZInQKernel/Cleanup.lean` (imported from `ZInQKernel.lean`). No existing file was edited
apart from that one import line. `lake build ZInQKernel` succeeds. `#print axioms` on every main
declaration below gives only `propext`, `Classical.choice`, `Quot.sound`. Nothing uses `sorry`,
`native_decide` or a finite-check hypothesis.

## Articles

| article path | Lean name | status |
| --- | --- | --- |
| model/field/fixed-point-codes.md | `ZInQ.iota_eq_psi_unconditional` | proved |
| assembly/approximation/real-accumulation.md | `ZInQ.Assembly.exists_multiple_large_unconditional` | proved |
| model/descent/nonzero-multiples.md | `ZInQ.genP0_not_isOfFinAddOrder`, `ZInQ.iota_injective` (existing); `ZInQ.zsmul_genP0_affine`, `ZInQ.zsmul_genP0_affine_z_w`, `ZInQ.iota_zero_coord_iff` (new); also `ZInQ.mult_zCoord_zsmul_genP0_ne_zero`, `ZInQ.mult_wCoord_zsmul_genP0_ne_zero`, `ZInQ.zIdx_ne_zero_of_ne_zero` | proved |
| syntax/templates/guard-semantics.md | `ZInQ.Syntax.guardTemplate_rel_codes3_iff` (the article's form), `ZInQ.Syntax.guardTemplate_rel_iff_not_falseTriple_guardPoly` (the `FalseTripleCodes` form) | proved |
| model/field/explicit-identities.md | `ZInQ.k0_identities` (items 1–5), `ZInQ.K0.totallyPositive_iff` (the positivity criterion), `ZInQ.k0_signs` (the sign consequences of item 4) | proved |
| compiler/natural/formulas/hierarchical-calls.md | items 1–2: `ZInQ.Compiler.Natural.toCircuit_item1`, `toCircuit_natRel_iff` (existing); item 3: `ZInQ.Compiler.Natural.toCircuit_natRel_iff_of_mspec`, `toCircuit_natRel_iff_of_spec`, `toCircuit_andM_natRel_iff` (new) | proved (item 3 in the reading explained below) |

Bridges (item 7 of the task, and item 6):

| bridge | Lean name |
| --- | --- |
| `W_A = shortCurve A` | `ZInQ.WA_eq_shortCurve` (rfl). `ZInQ.genCurve_eq_WA : genCurve = WA genA` already existed in `Model/DivisionPolynomials/MulByN.lean` |
| `iota m 0 = 0 ↔ m ≠ 0` | `ZInQ.iota_zero_coord_iff` (and `ZInQ.iota_zero_coord_eq_one_iff : iota m 0 = 1 ↔ m = 0`) |
| `zPt = Assembly.zCoord` | `ZInQ.zPt_eq_assembly_zCoord` (equality of functions) |
| `zPt = Mult.zCoord` on `E(K₀)` | `ZInQ.zPt_eq_mult_zCoord`, `ZInQ.assembly_zCoord_eq_mult_zCoord` (pointwise: `Mult.zCoord` is typed on `(shortCurve A).toAffine.Point`) |
| `σ±(u + v s) = u ± v√2` | `ZInQ.K0.embPlus_mk`, `embMinus_mk` (for `⟨u, v⟩`), `embPlus_add_mul_sqrt2`, `embMinus_add_mul_sqrt2` (for `↑u + ↑v * sqrt2`); `embPlus_apply` and `embMinus_apply` already existed |
| `ε_l ≤ \|σ₊ z_l\| + \|σ₋ z_l\|` | `ZInQ.Compiler.Precision.epsIdx_le_emb` (in ℝ), from `ZInQ.K0.abs_re_add_abs_im_le` |
| `r(a, j) = (σ₊ + σ₋)(z_j/z_a)/2` | `ZInQ.Compiler.Precision.rRatio_eq_half_emb_sum` (in ℝ), from `ZInQ.K0.re_eq_half_emb_sum` |

## Statement notes and corrections

- **fixed-point-codes, real-accumulation**: the existing conditional theorems with
  `genP0_not_isOfFinAddOrder` plugged in. Each statement matches its article exactly.
- **nonzero-multiples**: the implementation note's draft names `iota_injective'` and
  `iota_fin_iff` are not used. `ZInQ.iota_injective` is already unconditional, and the
  first-coordinate claim is `iota_zero_coord_iff`, the name the cross-chapter audit asked for.
  `z` and `w` are stated three ways: explicitly as `-x/y ≠ 0`, `1/x ≠ 0`
  (`zsmul_genP0_affine_z_w`); through the multiplication chapter's `Mult.zCoord`, `Mult.wCoord`;
  and as `zIdx m ≠ 0` (precision chapter). The affine-with-nonzero-ordinate part reuses
  `Compiler.Precision.admissible_of_ne_zero`.
- **guard-semantics**: the repository has no `Constructors` record for the specification yet
  (no `Constructors` value is defined anywhere). The templates are parametric in
  `I : Constructors E`, so the theorems take the hypothesis `hI : I.guard T = guardPoly T`.
  Once the specification's constructor record exists with `guard := guardPoly`, `hI` is `rfl`.
  The bridge between the two triple encodings is `ZInQ.Syntax.tripleCode_eq_codes3`
  (`tripleCode (a, b, c) = codes3 (ι a) (ι b) (ι c)`). The article's zero-set sentence is
  `ZInQ.Syntax.guardPoly_eval_eq_zero_iff_falseTripleCodes`.
- **explicit-identities**: integers are stated in ℤ. Item 3's `d ε⁴ = δ` is stated both as
  `genD * epsilon ^ 4 = delta` and literally as `⟨75, -53⟩ * ⟨17, 12⟩ = ⟨3, -1⟩`. Item 5 also
  records `392² = 153664`. The bounds `σ±(δ) ∈ [1, 5]` reuse `ZInQ.embPlus_delta_mem` and
  `ZInQ.embMinus_delta_mem` (`Model/Heights/DuplicationForms.lean`, stated as
  `1 ≤ _ ∧ _ ≤ 5`). The note's other projection names that already existed were reused:
  `genD_sq`, `norm_genD`, `epsilon_pow_four`, `epsilon_pow_six`, `delta_sq`,
  `totallyPositive_genD`, `totallyPositive_delta`, `signVector_epsilon`. New:
  `norm_delta`, `norm_sqrt2`, `genD_mul_epsilon_pow_four`.
- **hierarchical-calls, item 3**: proved in general, with "the conjunction of the relations of
  the macros of the construction, quantified over the remaining fresh variables" formalized
  as the relation `R` of a macro specification `MSpec τ m {i | i < k} R`. The macro-semantics
  file builds such specifications compositionally: `lt_spec` … `bitAnd_spec` and
  `powerSpec_hierarchical` for the macros, `MSpec.fresh_bind` for a fresh variable (giving
  `∃ z, R (update x c z)`), and `MSpec.note_bind`, `MSpec.expr_bind`, `MSpec.andM`,
  `MSpec.orM` for the other steps. `toCircuit_natRel_iff_of_mspec` then gives
  `Z_𝒞(c) ↔ R x` for any `x` equal to `c` on the inputs, under the node-encoding validity
  hypothesis of item 1. `toCircuit_andM_natRel_iff` is the special case of a conjunction of
  macros. This is the step that `Packed.compiled_natRel_iff` performs inline.
  Suggested wording for the article: "3. consequently, if the construction has macro
  specification `R` over the inputs (built from the macro semantics by the composition rules),
  `Z_𝒞(c) ⟺ R(c)`". A literal reading, where `R` is computed from a syntactic list of macro
  invocations, would need a separate AST of constructions; nothing in the chapter needs it.

## Item 8 (irreducible constants)

No change was needed. `ZInQKernel/Syntax/Constants/Fixed.lean:144` already declares
`attribute [irreducible] Ps W Hcat Hmax Ns M0 cstar ell F D G0 E0 R Q Bcm Ccm Aht T` right after
the equation lemmas. A global `attribute` command is exported to importing modules, and no
file in `ZInQKernel/` contains `unseal`, `semireducible` or a local reducibility override.
Note that `irreducible` only stops elaborator unfolding (`simp`, `rfl`, `decide` elaboration);
the kernel ignores it, so the "same definitional height" care of
`Compiler/Precision/HeightConstant.lean` is still needed for kernel checks. The parallel
constants `heightD`, `heightE0`, `heightBcm`, `heightCcm` in `Hypotheses/Height.lean` are not
irreducible. That file is part of the frozen hypotheses, so I left it alone.

## Problems

- None blocking. `Multiplication/Local/FormalLogarithm.lean:58` on main still declares a
  `sorry` (another task's file); none of my declarations depends on it.

## Suggestions for the next agent

- When the specification's `Constructors` value is defined, add the one-line corollary of
  `guardTemplate_rel_codes3_iff` with `hI := rfl`.
- Record `iota_eq_psi_unconditional` and `exists_multiple_large_unconditional` as the `lean:`
  fields of the two articles. Downstream users of the conditional versions can switch to
  these and drop the hypothesis.
