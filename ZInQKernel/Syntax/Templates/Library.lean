import ZInQKernel.Syntax.Templates.Value

/-!
# The template library

The ordered list of the 23 templates of the specification. The fixed constants enter as the
integer values `c_* = val(cstar)`, `ℓ = val(ell)`, `T = val(T)` and the program literal `c_3` of
the natural precision polynomial, which stay symbolic; the five integer constants of the
model-evaluation translation are `(4, 2, 3, c_3, 1399)`.
-/

namespace ZInQ.Syntax

variable {E : Type}

/-- The integer constants `integer_constant_0, …, integer_constant_4 = 4, 2, 3, c_3, 1399` of
the model-evaluation translation, in order of first occurrence. -/
def integerConstants (c3 : ℤ) : List ℤ := [4, 2, 3, c3, 1399]

/-- **The template library**: `member`, `raw_add`, `raw_z`, `raw_inverse_x`, `log25`, `pole`,
`test_group`, `slope`, `height_certificate`, `multiply.scalar = S_{c_*}`, `multiply.guard`,
`multiply`, `natural`, `value.signed_encode`, `value.abs`, `value.close_coordinates`,
`value.test`, `value.exceptions`, and `scalar.integer_constant_k = S_{integer_constant_k}` for
`k = 0, …, 4` (indices `0, …, 22`). -/
noncomputable def templateLibrary (I : Constructors E) (cstar ell T c3 : ℤ) : List ExPoly :=
  [memberTemplate, rawAddTemplate, rawZTemplate, rawInverseXTemplate, log25Template, poleTemplate,
    testGroupTemplate, slopeTemplate, heightTemplate, scalarTemplate I cstar, guardTemplate I T,
    multiplyTemplate I cstar ell T, naturalTemplate I cstar ell T,
    signedEncodeTemplate I cstar ell T, absTemplate, closeTemplate,
    valueTestTemplate I cstar ell T, exceptionsTemplate] ++
  (integerConstants c3).map (scalarTemplate I)

variable (I : Constructors E) (cstar ell T c3 : ℤ)

theorem length_templateLibrary : (templateLibrary I cstar ell T c3).length = 23 := rfl

/-- The parameter counts of the library. -/
theorem templateLibrary_params : (templateLibrary I cstar ell T c3).map ExPoly.params =
    [5, 15, 7, 7, 4, 1, 44, 22, 36, 10, 15, 15, 5, 10, 2, 16, 11, 6, 10, 10, 10, 10, 10] := rfl

/-- The witness counts of the library (the table of the template-library article). -/
theorem templateLibrary_witnesses : (templateLibrary I cstar ell T c3).map ExPoly.witnesses =
    [7, 6, 1, 0, 0, 11, 162, 1298, 35106, 1, 1, 35134, 140604, 140654, 4, 53, 35282, 406,
      1, 1, 1, 1, 1] := by
  simp only [templateLibrary, integerConstants, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, memberTemplate_witnesses, rawAddTemplate_witnesses,
    rawZTemplate_witnesses, rawInverseXTemplate_witnesses, log25Template_witnesses,
    poleTemplate_witnesses, testGroupTemplate_witnesses, slopeTemplate_witnesses,
    heightTemplate_witnesses, scalarTemplate_witnesses, guardTemplate_witnesses,
    multiplyTemplate_witnesses, naturalTemplate_witnesses, signedEncodeTemplate_witnesses,
    absTemplate_witnesses, closeTemplate_witnesses, valueTestTemplate_witnesses,
    exceptionsTemplate_witnesses]

/-- Every template of the library is well formed. -/
theorem templateLibrary_wf : ∀ τ ∈ templateLibrary I cstar ell T c3, τ.WF := by
  simp only [templateLibrary, integerConstants, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨memberTemplate_wf, rawAddTemplate_wf, rawZTemplate_wf, rawInverseXTemplate_wf,
    log25Template_wf, poleTemplate_wf, testGroupTemplate_wf, slopeTemplate_wf, heightTemplate_wf,
    scalarTemplate_wf I cstar, guardTemplate_wf I T, multiplyTemplate_wf I cstar ell T,
    naturalTemplate_wf I cstar ell T, signedEncodeTemplate_wf I cstar ell T, absTemplate_wf,
    closeTemplate_wf, valueTestTemplate_wf I cstar ell T, exceptionsTemplate_wf,
    scalarTemplate_wf I 4, scalarTemplate_wf I 2, scalarTemplate_wf I 3, scalarTemplate_wf I c3,
    scalarTemplate_wf I 1399⟩

/-- The scalar-constant templates at indices `18, …, 22`. -/
theorem getEx_templateLibrary_scalar (k : Fin 5) :
    getEx (templateLibrary I cstar ell T c3) (18 + k) =
      scalarTemplate I ((integerConstants c3).get ⟨k, by simp [integerConstants]⟩) := by
  fin_cases k <;> rfl

/-- The coefficients of the truncated logarithm: `(4j + 1) c_j = 16575 (-1)^j binom(2j, j)` for
`j = 0, …, 6`. -/
theorem log25Coeffs_spec : ∀ j : Fin 7,
    (4 * (j : ℤ) + 1) * log25Coeffs.get ⟨j, by simp [log25Coeffs]⟩ =
      16575 * (-1) ^ (j : ℕ) * ((2 * (j : ℕ)).choose j : ℤ) := by
  decide

end ZInQ.Syntax
