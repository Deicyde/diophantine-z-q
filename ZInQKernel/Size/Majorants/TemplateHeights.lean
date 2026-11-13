import ZInQKernel.Size.Majorants.Templates

/-!
# Template heights

Blueprint: `size/majorants/template-heights.md`, with `size/majorants/node-majorant.md` for
the constructed library.

The constructed library `templateLibrary I c_* ℓ T c_3` satisfies the height majorant at the
tabulated heights of the blueprint (`templateLibrary_maj`), for every `B ≥ 2^20` that
satisfies the node hypotheses of the template majorant (`LibraryAdmissible`):

* the uniform constructor bounds at `B` (`ConstructorBounds`);
* every psi index `n` that occurs has `|n| + 1 ≤ B`: by construction the psi nodes occur only
  in the fixed-scalar templates `S_ε`, `ε ∈ {c_*, 4, 2, 3, c_3, 1399}`, with the indices `ε`,
  `ε + 1`, `ε + (-1)` and `2ε` (`psiIndices`);
* the fixed node `ℓ` has `|ℓ| ≤ B - 1`;
* the guard node has cutoff `0 ≤ T ≤ B - 1`.

The literal constants of the templates (all below `2^69`) need no hypothesis: they enter the
size calculus at a level independent of `B`. The heights proved for the Lean templates
(`templateLeanHeights`, at most `8`) are far below the tabulated ones; the tabulated heights
follow by monotonicity.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {E : Type} {B : ℕ}

/-- The tabulated template heights of the blueprint, in library order: `member`, `raw_add`,
`raw_z`, `raw_inverse_x`, `log25`, `pole`, `test_group`, `slope`, `height_certificate`,
`multiply.scalar`, `multiply.guard`, `multiply`, `natural`, `value.signed_encode`,
`value.abs`, `value.close_coordinates`, `value.test`, `value.exceptions`,
`scalar.integer_constant_0`, …, `scalar.integer_constant_4`. -/
def templateHeightTable : List ℕ :=
  [18, 21, 12, 12, 25, 24, 79, 169, 207, 17, 4, 214, 223, 230, 9, 34, 249, 43, 17, 17, 17, 17, 17]

/-- The heights proved for the templates of the Lean library, in library order. -/
def templateLeanHeights : List ℕ :=
  [1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 6, 7, 8, 1, 2, 7, 2, 2, 2, 2, 2, 2]

/-- The psi indices of the library: `ε`, `ε + 1`, `ε + (-1)` and `2ε` for the scalars
`ε = c_*, 4, 2, 3, c_3, 1399` of the fixed-scalar templates. -/
def psiIndices (cstar c3 : ℤ) : List ℤ :=
  (cstar :: integerConstants c3).flatMap fun ε => [ε, ε + 1, ε + -1, 2 * ε]

/-- The hypotheses of the template majorant for the constructed library at the bound `B`. -/
structure LibraryAdmissible (B : ℕ) (I : Constructors E) (cstar ell T c3 : ℤ) : Prop where
  two_pow_le : 2 ^ 20 ≤ B
  constructors : ConstructorBounds I B
  psi : ∀ n ∈ psiIndices cstar c3, n.natAbs + 1 ≤ B
  fixed : ell.natAbs + 1 ≤ B
  guard : 0 ≤ T ∧ T.natAbs + 1 ≤ B

namespace LibraryAdmissible

variable {I : Constructors E} {cstar ell T c3 : ℤ} (h : LibraryAdmissible B I cstar ell T c3)
include h

theorem scalar_maj {ε : ℤ} (hε : ε ∈ cstar :: integerConstants c3) :
    Maj B 2 (scalarTemplate I ε).poly := by
  have hB1 := one_le_of_two_pow_twenty_le h.two_pow_le
  refine scalarTemplate_maj h.two_pow_le I ε fun m hm c => ?_
  have hm' : m ∈ psiIndices cstar c3 := List.mem_flatMap.2 ⟨ε, hε, hm⟩
  exact sz_of_constructor_bound hB1 (h.constructors.psi m (h.psi m hm') c)

theorem guard_maj : Maj B 2 (guardTemplate I T).poly :=
  guardTemplate_maj h.two_pow_le I T (sz_of_constructor_bound
    (one_le_of_two_pow_twenty_le h.two_pow_le) (h.constructors.guard T h.guard.1 h.guard.2))

theorem multiply_maj : Maj B 6 (multiplyTemplate I cstar ell T).poly :=
  multiplyTemplate_maj h.two_pow_le (h.scalar_maj List.mem_cons_self) h.guard_maj
    (sz_C_of_le (natAbs_le_two_pow_pow_eight h.fixed))

theorem natural_maj : Maj B 7 (naturalTemplate I cstar ell T).poly :=
  naturalTemplate_maj h.two_pow_le h.multiply_maj

end LibraryAdmissible

/-- **The templates of the library satisfy the majorant** at the heights proved for the Lean
templates. -/
theorem templateLibrary_maj_lean {I : Constructors E} {cstar ell T c3 : ℤ}
    (h : LibraryAdmissible B I cstar ell T c3) :
    ∀ i < 23, Maj B (templateLeanHeights.getD i 0) (getEx (templateLibrary I cstar ell T c3) i).poly := by
  have hB := h.two_pow_le
  have hint : ∀ k : ℕ, (hk : k < 5) →
      Maj B 2 (scalarTemplate I ((integerConstants c3).get ⟨k, by simp [integerConstants]; omega⟩)).poly :=
    fun k hk => h.scalar_maj (List.mem_cons_of_mem _ (List.get_mem _ _))
  intro i hi
  interval_cases i
  · exact memberTemplate_maj hB
  · exact rawAddTemplate_maj hB
  · exact rawZTemplate_maj hB
  · exact rawInverseXTemplate_maj hB
  · exact log25Template_maj hB
  · exact poleTemplate_maj hB
  · exact testGroupTemplate_maj hB
  · exact slopeTemplate_maj hB
  · exact heightTemplate_maj hB
  · exact h.scalar_maj List.mem_cons_self
  · exact h.guard_maj
  · exact h.multiply_maj
  · exact h.natural_maj
  · exact signedEncodeTemplate_maj hB h.natural_maj
  · exact absTemplate_maj hB
  · exact closeTemplate_maj hB
  · exact valueTestTemplate_maj hB h.multiply_maj
  · exact exceptionsTemplate_maj hB
  · exact hint 0 (by norm_num)
  · exact hint 1 (by norm_num)
  · exact hint 2 (by norm_num)
  · exact hint 3 (by norm_num)
  · exact hint 4 (by norm_num)

theorem templateLeanHeights_le_table :
    ∀ i < 23, templateLeanHeights.getD i 0 ≤ templateHeightTable.getD i 0 := by
  decide

/-- **Template heights.** For an admissible bound `B`, every template of the constructed
library satisfies the height majorant at its tabulated height. -/
theorem templateLibrary_maj {I : Constructors E} {cstar ell T c3 : ℤ}
    (h : LibraryAdmissible B I cstar ell T c3) :
    ∀ i < 23, Maj B (templateHeightTable.getD i 0) (getEx (templateLibrary I cstar ell T c3) i).poly :=
  fun i hi => (templateLibrary_maj_lean h i hi).mono (templateLeanHeights_le_table i hi)
    (one_le_of_two_pow_twenty_le h.two_pow_le)

end ZInQ.Size
