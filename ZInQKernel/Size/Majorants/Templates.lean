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
    (h : C.totalDegree ≤ B ^ 4 ∧ l1 C ≤ 2 ^ B ^ 8) : Scale B 8 0 C := by
  refine ⟨?_, ?_⟩
  · rw [pow_zero, one_mul]; exact h.1.trans (Nat.pow_le_pow_right hB (by norm_num))
  · rw [pow_zero, one_mul]; exact h.2

/-- A fixed constant with `|c| ≤ 2^(B^8)` is at level `(8, 0)`. -/
theorem sz_C_of_le {c : ℤ} (hc : c.natAbs ≤ 2 ^ B ^ 8) : Scale B 8 0 (C c : Poly) := by
  refine ⟨?_, ?_⟩
  · rw [totalDegree_C]; exact Nat.zero_le _
  · rw [l1_C, pow_zero, one_mul]; exact hc

section

variable (hB : 2 ^ 20 ≤ B) (I : Constructors E)
include hB

/-- The fixed-scalar template `S_n`, given level bounds for `Ψ_n`, `Ψ_{n+1}`, `Ψ_{n-1}` and
`Ψ_{2n}`. -/
theorem scalarTemplate_maj (n : ℤ)
    (hψ : ∀ m ∈ [n, n + 1, n + -1, 2 * n], ∀ c, Scale B 8 0 (I.psi m c)) :
    Maj B 2 (scalarTemplate I n).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have h0 : ∀ c, Scale B 8 0 (I.psi n c) := hψ n (by simp)
  have h1 : ∀ c, Scale B 8 0 (I.psi (n + 1) c) := hψ (n + 1) (by simp)
  have h2 : ∀ c, Scale B 8 0 (I.psi (n + -1) c) := hψ (n + -1) (by simp)
  have h3 : ∀ c, Scale B 8 0 (I.psi (2 * n) c) := hψ (2 * n) (by simp)
  rw [scalarTemplate_poly]
  size_maj

/-- The guard template, given a level bound for `G_T`. -/
theorem guardTemplate_maj (T : ℤ) (hG : Scale B 8 0 (I.guard T)) :
    Maj B 2 (guardTemplate I T).poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  rw [guardTemplate_poly]
  size_maj

variable {I} {cstar ell T : ℤ}

theorem multiplyTemplate_maj (hS : Maj B 2 (scalarTemplate I cstar).poly)
    (hG : Maj B 2 (guardTemplate I T).poly) (hℓ : Scale B 8 0 (C ell : Poly)) :
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

/-! ### The exceptional values -/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {B : ℕ}

/-- A rational constant of a construction is a variable or the constant `u`. -/
theorem sz_rational (hB : 1 ≤ B) (k : ℕ) {u q : ℤ} (hu : u.natAbs ≤ 2 ^ 2 ^ k)
    (s : BuildState) : Scale B 0 k (Build.rational u q s).1 := by
  unfold Build.rational
  dsimp only
  split_ifs
  · refine Scale.C hB ?_
    unfold Build.normalize
    split_ifs <;> simpa using hu
  · split
    · exact (Scale.X hB _).mono hB le_rfl (Nat.zero_le _)
    · exact (Scale.X hB _).mono hB le_rfl (Nat.zero_le _)

theorem asz_gen (hB : 1 ≤ B) (s : BuildState) : AScale B 0 5 (Build.gen s).1 := by
  have hrat : ∀ (u q : ℤ) (s : BuildState), u.natAbs ≤ 2 ^ 2 ^ 5 →
      Scale B 0 5 (Build.rational u q s).1 := fun u q s hu => sz_rational hB 5 hu s
  simp only [Build.gen, Build.bind_apply, Build.pure_apply]
  intro k
  size_le

theorem length_binDigitsAux : ∀ fuel k, (binDigitsAux fuel k).length ≤ fuel
  | 0, _ => le_rfl
  | fuel + 1, k => by
    rw [binDigitsAux]
    split_ifs
    · exact Nat.zero_le _
    · simpa using length_binDigitsAux fuel (k / 2)

theorem length_binDigits (k : ℕ) : (binDigits k).length ≤ k := length_binDigitsAux k k

/-- The double-and-add chain: its value stays at the level of its inputs, its formulas are
raw-addition calls one level higher, and there are at most two per digit. -/
theorem chainBuild_sz (hB : 1 ≤ B) {a : ℕ} (hR : Scale B 8 0 rawAddTemplate.poly) :
    ∀ (ds : List Bool) (out base : Code) (s : BuildState), AScale B 0 a out → AScale B 0 a base →
      AScale B 0 a (chainBuild out base ds s).1.1 ∧ FAll B 8 (a + 1) (chainBuild out base ds s).1.2 ∧
        (chainBuild out base ds s).1.2.length ≤ 2 * ds.length := by
  have hcall : ∀ (p q r : Code) (w : ℕ), AScale B 0 a p → AScale B 0 a q → AScale B 0 a r →
      FAll B 8 (a + 1) [Formula.call rawAddTemplate (Fin.append (Fin.append p q) r) w] := by
    intro p q r w hp hq hr φ hφ
    rw [List.mem_singleton] at hφ
    subst hφ
    have := Scale.compile_call' (w := w) hB hR ((hp.append' hB hq).append' hB hr)
    exact this.mono hB (by simp) (by simp)
  have happ : ∀ {l₁ l₂ : List Formula}, FAll B 8 (a + 1) l₁ → FAll B 8 (a + 1) l₂ →
      FAll B 8 (a + 1) (l₁ ++ l₂) := fun h₁ h₂ φ hφ => by
    rcases List.mem_append.1 hφ with hφ | hφ
    exacts [h₁ φ hφ, h₂ φ hφ]
  have hpt : ∀ k, AScale B 0 a (varPoint k) := fun k =>
    (AScale.varPoint hB k).mono hB le_rfl (Nat.zero_le _)
  intro ds
  induction ds with
  | nil =>
    intro out base s hout _
    exact ⟨hout, FAll.nil_mono' _ _, by simp [chainBuild]⟩
  | cons d ds ih =>
    intro out base s hout hbase
    cases d with
    | false =>
      cases ds with
      | nil =>
        exact ⟨hout, FAll.nil_mono' _ _, by simp [chainBuild]⟩
      | cons d' ds' =>
        obtain ⟨h1, h2, h3⟩ := ih out (varPoint (s.next)) { s with next := s.next + 5 + 6 }
          hout (hpt _)
        refine ⟨h1, happ (happ (FAll.nil_mono' _ _) (hcall _ _ _ (s.next + 5) hbase hbase
          (hpt _))) h2, ?_⟩
        show ([] ++ [_] ++ (chainBuild out (varPoint s.next) (d' :: ds')
          { s with next := s.next + 5 + 6 }).1.2).length ≤ _
        simp only [List.length_append, List.length_nil, List.length_cons] at h3 ⊢
        omega
    | true =>
      cases ds with
      | nil =>
        exact ⟨hpt _, hcall _ _ _ _ hout hbase (hpt _), by simp [chainBuild]⟩
      | cons d' ds' =>
        obtain ⟨h1, h2, h3⟩ := ih (varPoint s.next) (varPoint (s.next + 5 + 6))
          { s with next := s.next + 5 + 6 + 5 + 6 } (hpt _) (hpt _)
        refine ⟨h1, happ (happ (hcall _ _ _ (s.next + 5) hout hbase (hpt _))
          (hcall _ _ _ (s.next + 5 + 6 + 5) hbase hbase (hpt _))) h2, ?_⟩
        simp only [chainBuild, Build.bind_apply, Build.pure_apply, Build.point, Build.call,
          rawAddTemplate_witnesses, List.length_append, List.length_cons, List.length_nil] at h3 ⊢
        omega

/-- A branch `β_c` of `value.exceptions` for `|c| ≤ 60`. -/
theorem exceptionBranch_sz (hB : 1 ≤ B) (hR : Scale B 8 0 rawAddTemplate.poly) {N : Code}
    (hN : AScale B 0 0 N) {t : Poly} (ht : Scale B 0 0 t) (c : ℤ) (hc : c.natAbs ≤ 60)
    (s : BuildState) : Scale B 8 17 (exceptionBranch N t c s).1.compile := by
  have hG := asz_gen hB s
  have hbase : AScale B 0 5 (if c < 0 then (Build.gen s).1.neg else (Build.gen s).1) := by
    split_ifs
    · exact hG.neg
    · exact hG
  obtain ⟨hv, hfs, hlen⟩ := chainBuild_sz (a := 5) hB hR (binDigits c.natAbs) Code.O
    (if c < 0 then (Build.gen s).1.neg else (Build.gen s).1) (Build.gen s).2
    ((AScale.O hB).mono hB le_rfl (Nat.zero_le 5)) hbase
  have hlen' : (chainBuild Code.O (if c < 0 then (Build.gen s).1.neg else (Build.gen s).1)
      (binDigits c.natAbs) (Build.gen s).2).1.2.length ≤ 2 ^ 7 :=
    hlen.trans (by have := length_binDigits c.natAbs; omega)
  simp only [exceptionBranch, fixedMultipleBuild, Build.bind_apply, Build.pure_apply]
  generalize (chainBuild Code.O (if c < 0 then (Build.gen s).1.neg else (Build.gen s).1)
      (binDigits c.natAbs) (Build.gen s).2).1 = r at hv hfs hlen' ⊢
  obtain ⟨v, fs⟩ := r
  dsimp only at hv hfs hlen' ⊢
  have hc' : c.natAbs ≤ 2 ^ 2 ^ 3 := hc.trans (by norm_num)
  size_le

theorem exceptionsTemplate_maj (hB : 2 ^ 20 ≤ B) : Maj B 2 exceptionsTemplate.poly := by
  have hB1 : 1 ≤ B := one_le_of_two_pow_twenty_le hB
  have hm := (memberTemplate_maj hB).sz
  have hR : Scale B 8 0 rawAddTemplate.poly := (rawAddTemplate_maj hB).sz
  have hb : ∀ (c : ℤ) (s : BuildState), c.natAbs ≤ 60 →
      Scale B 8 17 (exceptionBranch (varPoint 0) (X 5) c s).1.compile := fun c s hc =>
    exceptionBranch_sz hB1 hR (AScale.varPoint hB1 0) (Scale.X hB1 5) c hc s
  rw [exceptionsTemplate, Build.template_poly, Build.fullFormula, exceptions_facts.globalsEq]
  simp only [exceptionsGlobals, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    exceptionsBuild, Build.bind_apply, Build.pure_apply]
  size_maj

end ZInQ.Size
