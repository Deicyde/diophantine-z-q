# h-min: hypothesis H weakened to the one inequality the proof uses

Branch `wip/h-min`, from `origin/main` with `origin/wip/rs-height` merged.
`lake build ZInQKernel` passes, `python3 scripts/check_target.py` passes, and
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
`exists_bounded_integer_polynomial_defining_integers_of`, `_of_sixContactEstimate`,
`_of_twoSlopePattern`, `_of_nodeCheck` and `sixContactMin_of_sixContactEstimate`.
No `sorry`, no new finite checks.

## New main-theorem statement

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) : FrozenTarget

def ZInQ.SixContactMin : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport Mult.S_mul u : ℝ) ^ 24
```

The manuscript form is still available:

```lean
theorem ZInQ.sixContactMin_of_sixContactEstimate (hH : SixContactEstimate) : SixContactMin
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) : FrozenTarget
```

## Table

| article path | Lean name | status |
| --- | --- | --- |
| (new; no article) | `ZInQ.SixContactMin` (`Hypotheses/HeightMin.lean`) | definition |
| (new; no article) | `ZInQ.sixContactMin_of_sixContactEstimate` (`Main.lean`) | proved |
| main/main-theorem.md | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` | proved; hypothesis now `SixContactMin` |
| main/main-theorem.md | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate` | proved (new corollary, manuscript form) |
| compiler/natural/precision/precision-height-constant.md | `ZInQ.Compiler.Precision.sixContact_at_heightPrimes` | proved from `SixContactMin`; moved to `Hypotheses/HeightMin.lean` |
| multiplication/certificate/constants-properties.md | `ZInQ.Mult.sixContact_at_Smul` | proved from `SixContactMin` |
| multiplication/soundness/contact-support.md | `ZInQ.Mult.slope_height_le_of`, `ZInQ.Mult.slope_height_le` | proved; `_of` signature generalized (see below) |
| main/six-contact-estimate.md | `ZInQ.SixContactEstimate` | unchanged; no longer a hypothesis of the main theorem |

## Changed signatures

Only `hH : SixContactEstimate` became `hH : SixContactMin` in all of these, nothing else:

- `Main.lean`: `exists_bounded_integer_polynomial_defining_integers_of_addMulBound`,
  `_of_nodeCheck`, `exists_bounded_integer_polynomial_defining_integers_of`, `_of_twoSlopePattern`.
- `Assembly/Top/Assembly.lean`: `Assembly.Pstar_spec`, `Assembly.assembly`.
- `Assembly/Top/ValueRelation.lean`: `main_branch_eq_of`, `value_relation_iff_of`,
  `exists_value_relation_iff_of`, `main_branch_eq`, `value_relation_iff`, `exists_value_relation_iff`.
- `Assembly/Top/MainBranch.lean`: `ratHeight_le_bound_of_test`, `eq_of_close_of_test`.
- `Multiplication/Top/Exact.lean`: `Mult.multiplication_exact`, `Mult.multiplication_existsUnique`.
- `Multiplication/Soundness/MultiplySound.lean`: `Mult.multiply_sound`.
- `Multiplication/Soundness/FiniteBox.lean`: `Mult.finite_box_of_slopes`,
  `Mult.finite_box_of_heightCert`, `Mult.finite_box`.
- `Multiplication/Soundness/ContactSupport.lean`: `Mult.slope_height_le`.
- `Compiler.Precision.sixContact_at_heightPrimes`, `Mult.sixContact_at_Smul`: conclusions unchanged.

One signature changed shape:

```lean
-- before: (hH : SixContactEstimate) {S} (hSp) (hS) {R : ℝ} (hRD) (hRS) (hR12) ... ,
--         conclusion with heightH6 R
theorem Mult.slope_height_le_of {S : Finset ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hest : ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ A * (contactSupport S u : ℝ) ^ 24)
    {t ℓ : ℚ} {c₀ : ℤ} (hout : …) (n : Fin 3 → ℤ) (hf : n 0 * n 1 - n 2 ≠ 0)
    (hs : SlopePred t ℓ ![c₀, c₀ * n 0, c₀ * n 1, c₀ * n 2]) :
    ((contactSupport S t : ℕ) : ℤ) ^ 25 ∣ n 0 * n 1 - n 2 ∧
      ratHeight t ≤ A * |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25)
```

It now takes the six-contact bound for the one set `S` as a hypothesis, with any constant `A`,
in place of the full estimate plus the admissibility of `(S, R)`. The admissibility hypotheses
were used only to instantiate `hH`.

## Checking the rs-height note against the Lean (sections 1 and 2)

- Correct: H is consumed at exactly two places, and the threading files only pass `hH` on.
  The precision use is `sixContact_at_heightPrimes` (at `S_ht`, `D`), used only by
  `ratHeight_le_bound_of_test`. `M_{S_mul} ∣ M_{S_ht}`, `A0 = H₆(D)` (`A0_eq_heightH6`) and
  `max S_mul ≤ D` (from `Hmax_lt_D`, `cstar_lt_D`) all hold as stated.
- Correction: the multiplication use was not at `Mult.sixContact_at_Smul`, which had no
  consumer. It was at `Mult.slope_height_le_of`, which applied `hH` at a general admissible
  `(S, R)`. `slope_height_le` passed `S = S_mul`, `R = Syntax.R` to it. Now
  `slope_height_le_of` takes a bound for one fixed `S`, and `slope_height_le` feeds it
  `sixContact_at_Smul`, so the note's description holds after this change.
- Not used: `R_eq_D`. For the multiplication leaf I used monotonicity,
  `H₆(D) ≤ H₆(R) = A_ht` (`heightH6_mono_of_one_le`, with `D ≤ R` from `S_mul_admissible`). It
  holds without the catalogue bound, so the multiplication chapter does not import the
  `Progressions` library. `R = D` (through `catalogueBound8`) is used once, in
  `Mult.le_heightD_of_mem_S_mul`, for the admissibility in
  `sixContactMin_of_sixContactEstimate`.

## Why `SixContactMin` has this form

- **The constant is `heightH6 heightD`, not `Compiler.Precision.A0`.** It uses only the
  vocabulary of `Hypotheses/Height.lean`. A reader can then see that `SixContactMin` is the
  instance `S = S_mul`, `R = D` of `SixContactEstimate`: same left side, same `heightH6`,
  `R := heightD`. `A0_eq_heightH6` identifies it with `A0 = 2·10¹³ max(1, C_cm, Q₀¹⁷)`.
- **The prime set is the name `Mult.S_mul`.** Its defining expression is
  `S_ht ∪ 𝓗 ∪ supp(c_*)`, with `c_* = 4 M₀` and `M₀` the least formal multiple of `N_s`.
  Written out inline it would not be readable. The docstring of `HeightMin.lean` spells it out.
  As a result, `Hypotheses/HeightMin.lean` imports `Multiplication/Certificate/Constants.lean`.
  The hypothesis therefore depends on construction definitions, but not on any theorem: the
  catalogue bound is needed only to derive `SixContactMin` from `SixContactEstimate`.
- **Import cycle.** `HeightConstant.lean` sits upstream of `S_mul`, so
  `sixContact_at_heightPrimes` could not stay there. It now lives in `HeightMin.lean` under its
  old name, `ZInQ.Compiler.Precision.sixContact_at_heightPrimes`, with the same statement. A
  comment in `HeightConstant.lean` points to it.

## Lemmas added beyond the task list

All in namespace `ZInQ`, in `Hypotheses/HeightMin.lean` unless noted:
- `heightH6_nonneg`, `heightH6_mono_of_one_le` (`1 ≤ R ≤ R' → H₆(R) ≤ H₆(R')`).
- `contactSupport_pos`, `contactSupport_dvd_of_subset` (`S ⊆ S' → M_{S'}(u) ∣ M_S(u)`).
- `Mult.heightPrimes_subset_S_mul`.
- `Mult.le_heightD_of_mem_S_mul` (`Main.lean`): `p ∈ S_mul → p ≤ heightD`.

## Other edits

- `ZInQKernel.lean`: one added line, `import ZInQKernel.Hypotheses.HeightMin`.
- `KERNEL_PLAN.md`: the quoted main theorem now takes `SixContactMin`, with a paragraph on the
  corollary.
- Docstrings of `ConstantsProperties.lean`, `ContactSupport.lean` and `Main.lean` updated.

## For the lead (blueprint updates; I did not edit blueprint/)

- main/main-theorem.md: hypothesis H is now `ZInQ.SixContactMin`. Add
  `..._of_sixContactEstimate` and `sixContactMin_of_sixContactEstimate`. A new leaf for
  `SixContactMin` may be warranted, e.g. main/six-contact-min.md.
- multiplication/soundness/contact-support.md: the general form takes the bound
  `h ≤ A·M_S^24` for one `S` in place of the estimate and admissibility.
- compiler/natural/precision/precision-height-constant.md,
  multiplication/certificate/constants-properties.md: the six-contact items follow from
  `SixContactMin`; the precision lemma has moved to `Hypotheses/HeightMin.lean`.
- docs/kernel-audits/*: the binder lists quoted there are historical, and I left them alone.

## Problems

None. The first full build succeeded.

## Suggestions for the next agent

- `SixContactMin` could be weakened further, to the shape the note calls H_M or H_P (§2.2–2.3).
  The only consumers are `sixContact_at_heightPrimes`, through the precision program's constant
  `A0`, and `sixContact_at_Smul`, through `Aht` and `T`. Changing the constant or exponent means
  changing those programs and the size chain, not the threading.
- The audit documents under docs/kernel-audits/ list the old binders. A fresh audit should
  record `SixContactMin` as the H binder.
