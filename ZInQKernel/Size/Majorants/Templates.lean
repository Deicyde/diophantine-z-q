import ZInQKernel.Size.Majorants.Tactic
import ZInQKernel.Size.Majorants.NodeMajorant

/-!
# The templates of the library satisfy the height majorant

Blueprint: `size/majorants/template-heights.md` and `size/majorants/node-majorant.md`, for
the constructed library `ZInQ.Syntax.templateLibrary`.

The templates of the Lean library are `Build` programs, not node lists, so the intrinsic
heights of the blueprint are replaced by majorants proved template by template from the final
formulas (`*_formula`, `*_poly`), by the tactic `size` and the callee majorants. No build is
evaluated and no fixed value is computed: the fixed constants enter only through the
hypotheses `LibraryAdmissible` (the node hypotheses of the blueprint) and the uniform
constructor bounds.

The heights obtained here are much smaller than the tabulated ones of the blueprint (whose
node lists charge one level per node): a template without calls and constructors has
height `1`, a call costs one level beyond its callee, a constructor or the fixed constant `ℓ`
one more. The tabulated heights follow by monotonicity (`templateLibrary_maj`).
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {E : Type} {B : ℕ}

/-! ### Templates without calls -/

section

variable (hB : 2 ^ 20 ≤ B)
include hB

theorem memberTemplate_maj : Maj B 1 memberTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [memberTemplate_poly]
  size_maj

theorem rawAddTemplate_maj : Maj B 1 rawAddTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [rawAddTemplate_poly]
  size_maj

theorem rawZTemplate_maj : Maj B 1 rawZTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [rawZTemplate_poly]
  size_maj

theorem rawInverseXTemplate_maj : Maj B 1 rawInverseXTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [rawInverseXTemplate_poly]
  size_maj

theorem log25Template_maj : Maj B 1 log25Template.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [log25Template, Build.template_poly, Build.fullFormula, log25Build_run]
  size_maj

theorem poleTemplate_maj : Maj B 1 poleTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [poleTemplate_poly]
  size_maj

theorem absTemplate_maj : Maj B 1 absTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [absTemplate_poly]
  size_maj

/-! ### The certificate templates -/

theorem testGroupTemplate_maj : Maj B 2 testGroupTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := (memberTemplate_maj hB).sz
  have h1 := (rawAddTemplate_maj hB).sz
  have h2 := (rawZTemplate_maj hB).sz
  have h3 := (log25Template_maj hB).sz
  have h4 := (rawInverseXTemplate_maj hB).sz
  rw [testGroupTemplate, Build.template_poly, Build.fullFormula, testGroup_facts.globalsEq,
    testGroupBuild_formula, List.map_nil, List.nil_append]
  size_maj

theorem slopeTemplate_maj : Maj B 3 slopeTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := (testGroupTemplate_maj hB).sz
  have h1 := (poleTemplate_maj hB).sz
  rw [slopeTemplate, Build.template_poly, Build.fullFormula, slope_facts.globalsEq,
    slopeBuild_formula, List.map_nil, List.nil_append]
  size_maj

theorem heightTemplate_maj : Maj B 4 heightTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := (memberTemplate_maj hB).sz
  have h1 := (slopeTemplate_maj hB).sz
  rw [heightTemplate, Build.template_poly, Build.fullFormula, height_facts.globalsEq,
    heightBuild_formula, List.map_nil, List.nil_append]
  size_maj

theorem closeTemplate_maj : Maj B 2 closeTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := (memberTemplate_maj hB).sz
  have h1 := (absTemplate_maj hB).sz
  rw [closeTemplate, Build.template_poly, Build.fullFormula, close_facts.globalsEq,
    closeBuild_formula, List.map_nil, List.nil_append]
  size_maj

end

/-! ### Constructors -/

/-- A constructor with `deg C ≤ B^4` and `‖C‖₁ ≤ 2^(B^8)` is at level `(8, 0)`. -/
theorem sz_of_constructor_bound {σ : Type*} {C : MvPolynomial σ ℤ} (hB : 1 ≤ B)
    (h : C.totalDegree ≤ B ^ 4 ∧ l1 C ≤ 2 ^ B ^ 8) : Sz B 8 0 C := by
  refine ⟨?_, ?_⟩
  · rw [pow_zero, one_mul]; exact h.1.trans (Nat.pow_le_pow_right hB (by norm_num))
  · rw [pow_zero, one_mul]; exact h.2

/-- A fixed constant with `|c| ≤ 2^(B^8)` is at level `(8, 0)`. -/
theorem sz_C_of_le {c : ℤ} (hc : c.natAbs ≤ 2 ^ B ^ 8) : Sz B 8 0 (C c : Poly) := by
  refine ⟨?_, ?_⟩
  · rw [totalDegree_C]; exact Nat.zero_le _
  · rw [l1_C, pow_zero, one_mul]; exact hc

section

variable (hB : 2 ^ 20 ≤ B) (I : Constructors E)
include hB

/-- The fixed-scalar template `S_n`, given level bounds for `Ψ_n`, `Ψ_{n+1}`, `Ψ_{n-1}` and
`Ψ_{2n}`. -/
theorem scalarTemplate_maj (n : ℤ)
    (hψ : ∀ m ∈ [n, n + 1, n + -1, 2 * n], ∀ c, Sz B 8 0 (I.psi m c)) :
    Maj B 2 (scalarTemplate I n).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 : ∀ c, Sz B 8 0 (I.psi n c) := hψ n (by simp)
  have h1 : ∀ c, Sz B 8 0 (I.psi (n + 1) c) := hψ (n + 1) (by simp)
  have h2 : ∀ c, Sz B 8 0 (I.psi (n + -1) c) := hψ (n + -1) (by simp)
  have h3 : ∀ c, Sz B 8 0 (I.psi (2 * n) c) := hψ (2 * n) (by simp)
  rw [scalarTemplate_poly]
  size_maj

/-- The guard template, given a level bound for `G_T`. -/
theorem guardTemplate_maj (T : ℤ) (hG : Sz B 8 0 (I.guard T)) :
    Maj B 2 (guardTemplate I T).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [guardTemplate_poly]
  size_maj

variable {I} {cstar ell T : ℤ}

theorem multiplyTemplate_maj (hS : Maj B 2 (scalarTemplate I cstar).poly)
    (hG : Maj B 2 (guardTemplate I T).poly) (hℓ : Sz B 8 0 (C ell : Poly)) :
    Maj B 6 (multiplyTemplate I cstar ell T).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := hS.sz
  have h1 := hG.sz
  have h2 := (heightTemplate_maj hB).sz
  rw [multiplyTemplate, Build.template_poly, Build.fullFormula,
    (multiply_facts I cstar ell T).globalsEq, multiplyBuild_formula]
  simp only [multiplyGlobals, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  size_maj

theorem naturalTemplate_maj (hM : Maj B 6 (multiplyTemplate I cstar ell T).poly) :
    Maj B 7 (naturalTemplate I cstar ell T).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := hM.sz
  have h1 := (rawAddTemplate_maj hB).sz
  rw [naturalTemplate, Build.template_poly, Build.fullFormula,
    (natural_facts I cstar ell T).globalsEq, naturalBuild_formula, List.map_nil,
    List.nil_append]
  size_maj

theorem signedEncodeTemplate_maj (hN : Maj B 7 (naturalTemplate I cstar ell T).poly) :
    Maj B 8 (signedEncodeTemplate I cstar ell T).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := hN.sz
  have h1 := (rawAddTemplate_maj hB).sz
  have h2 := (memberTemplate_maj hB).sz
  rw [signedEncodeTemplate, Build.template_poly, Build.fullFormula,
    (signedEncode_facts I cstar ell T).globalsEq, signedEncodeBuild_formula]
  simp only [signedEncodeGlobals, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  size_maj

theorem valueTestTemplate_maj (hM : Maj B 6 (multiplyTemplate I cstar ell T).poly) :
    Maj B 7 (valueTestTemplate I cstar ell T).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 := hM.sz
  have h1 := (rawAddTemplate_maj hB).sz
  have h2 := (memberTemplate_maj hB).sz
  have h3 := (poleTemplate_maj hB).sz
  rw [valueTestTemplate, Build.template_poly, Build.fullFormula,
    (valueTest_facts I cstar ell T).globalsEq, valueTestBuild_formula, List.map_nil,
    List.nil_append]
  size_maj

end

end ZInQ.Size
