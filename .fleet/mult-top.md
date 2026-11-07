# mult-top report

## Leaves

| article path | Lean name | status |
|---|---|---|
| multiplication/multiplication-template.md | `ZInQ.Mult.multiplication_exact` (input M); uniqueness: `ZInQ.Mult.multiplication_exact_unique`, `ZInQ.Mult.multiplication_existsUnique` | proved |

`multiplication_exact` has exactly the requested form:

```lean
theorem ZInQ.Mult.multiplication_exact (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) :
    Translation.MultiplicationExact Syntax.specConstructors FixedConst.cstar.value
      FixedConst.ell.value FixedConst.T.value
```

`#print axioms` reports only `propext, Classical.choice, Quot.sound`. No sorry, no
finite-computation hypotheses.

Uniqueness comes in two forms. `multiplication_exact_unique`: if
`(Y₁,Y₂,Y₃) = (ι a, ι b, ι(ab)) = (ι a', ι b', ι(a'b'))` then `a = a' ∧ b = b'`.
`multiplication_existsUnique`: `Rel_multiply(Y₁,Y₂,Y₃) ↔ ∃! ab : ℤ × ℤ, Y₁ = ι ab.1 ∧ Y₂ = ι ab.2 ∧ Y₃ = ι(ab.1 ab.2)`.

## Statement corrections

None. The article matches `MultiplicationExact` with the specification's constructors and the
symbolic values of `c_*`, `ℓ`, `T`. The article's "15 parameters, 35134 witnesses" is not
restated: it is `multiplyTemplate_params` / `multiplyTemplate_witnesses` (Syntax chapter).

## Cleanup done

1. **`multiply_sound` / `multiply_complete` are now stated for `specConstructors` and the fixed
   constants**, with `FixedConst.cstar.value`, `FixedConst.ell.value`, `FixedConst.T.value`. That
   is the same form as `MultiplicationExact`. The hypotheses `hM0`, `hS` and `hI` are gone.
   - `multiply_sound (hH) (Y₁ Y₂ Y₃) (hY : (multiplyTemplate specConstructors c ℓ T).Rel (codes3 Y₁ Y₂ Y₃))`
   - `multiply_complete (hPC) (h22) (a b)`

   No other code used the general forms, so they were replaced, not kept. The blueprint names
   (`lean:` fields of soundness.md and completeness.md) are unchanged.
   `multiply_rel_iff`, `guard_true_triple` and `guard_false_triple` stay generic in `I`. They are
   unfolding lemmas, and their `lean:` fields name them in that form.
2. **`hM0 : 1 ≤ Syntax.M0` is removed from the whole chapter.** The new lemma
   `ZInQ.Mult.one_le_M0_spec : 1 ≤ Syntax.M0` in `Certificate/ConstantsProperties.lean` (from
   `Size.M0_bounds Syntax.Ns_pos`) replaces it. These lemmas lost the argument:
   `four_le_cstar`, `cstar_pos`, `not_mem_S_mul`, `local_congruence`, `slope_height_le`,
   `finite_box_of_slopes`, `finite_box_of_heightCert`, `finite_box`, `exists_shift`,
   `slope_complete`, `slopes_of_int`, `completeness_core`.
   `ConstantsProperties.lean` now imports `Size.FormalMultiple.Existence`. `one_le_M0` (from a
   formal multiple) is kept because constants-properties.md names it.
3. **Duplicate lemmas:**
   - `exists_prime_dvd_natCast_of_prime` (Completeness/PoleValuationsAux) is removed. Its one call
     site, in PoleValuations, now uses `Soundness/CommonGroup.lean`'s `exists_prime_dvd_natCast`
     (the `[Fact p.Prime]` form).
   - `mapE_mem_W1` (Soundness/TestsToCongruence) is removed. `mapE_mem_W1_of_mem` moved from
     Completeness/SelectedPrecision to TestsToCongruence, next to the new
     `zsmul_genP0_mem_W1_of_rhoAt` (`v_π(ρ([m]P₀)) ≥ 1 → [m]P₀ ∈ E₁`, stated over `K₀`). The
     old lemma is the composition of the two, and its call sites in `ratioAt_eq` use that.
   - `invDiffCoeff_succ_rec_aux`, `invDiffSeries_ode_aux` and `invDiffSeries_sq_aux`
     (FormalLog/InvDiff) are removed. The originals `invDiffCoeff_succ_rec`, `invDiffSeries_ode`
     and `invDiffSeries_sq` moved from Local/LogSeries to a new module,
     `Multiplication/Local/InvDiffSeries.lean` (it imports only Local/FormalLog). Both InvDiff
     and LogSeries import it. The names are unchanged, so logarithm-series.md's `lean:` field
     (`invDiffSeries_ode`) still resolves.

## Lemmas added beyond the leaf

- `ZInQ.Mult.spec_scalar_cstar_rel_iff`, in the new module `Multiplication/Certificate/Spec.lean`:
  the semantics of `S_{c_*}` for `specConstructors`
  (`Rel(ι m, r) ↔ r = ι(c_* m)`, from `scalarTemplate_rel_iff_iota` and `c_* ≥ 4`).
- `ZInQ.Mult.one_le_M0_spec` (ConstantsProperties).
- `ZInQ.Mult.zsmul_genP0_mem_W1_of_rhoAt` (TestsToCongruence).
- `ZInQ.Mult.multiplication_exact_unique`, `ZInQ.Mult.multiplication_existsUnique` (Top/Exact).

## Problems / notes for the lead and the next agent

- Two more copies of `exists_prime_dvd_natCast` sit outside this task's directories, so I left
  them alone. They are in other namespaces with the same statement:
  `Assembly/Local/TestDivisibility.lean:75`, with `(p) [Fact p.Prime]`, and
  `Size/FormalMultiple/OddCoefficients.lean:24`, with section variables. Size cannot import
  `Multiplication/Soundness/CommonGroup` cheaply. A natural home for one shared copy is
  `Multiplication/Local/PrimesAbove.lean`, which Size, Assembly and Soundness already import.
- Blueprint updates suggested:
  - multiplication-template.md: `lean: ZInQ.Mult.multiplication_exact, ZInQ.Mult.multiplication_exact_unique, ZInQ.Mult.multiplication_existsUnique`.
  - soundness.md and completeness.md: their proofs no longer take `M₀ ≥ 1` or the constructor
    facts as hypotheses.
  - constants-properties.md: add `one_le_M0_spec`.
