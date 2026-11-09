import ZInQKernel.Syntax.Templates.Multiply

/-!
# The value templates

Templates `13` (`value.signed_encode`), `14` (`value.abs`), `15` (`value.close_coordinates`),
`16` (`value.test`) and `17` (`value.exceptions`): `addVariableShiftTemplates` of
`construction/variable-shift-polynomial-library.js`, with `fixedMultiple` of
`construction/rational-model-assembly.js` for the chains of the exceptional values.
-/

namespace ZInQ.Syntax

open MvPolynomial

variable {E : Type}

/-! ### `value.abs` -/

/-- The construction of `value.abs` on `x`, `a`: four fresh `z_i`, then
`⋀(a ≐ z₁² + z₂² + z₃² + z₄², a² ≐ x²)`. -/
noncomputable def absBuild (x a : Poly) : Build Formula := do
  let z1 ← Build.fresh
  let z2 ← Build.fresh
  let z3 ← Build.fresh
  let z4 ← Build.fresh
  pure (.and [.eq a (z1 ^ 2 + z2 ^ 2 + z3 ^ 2 + z4 ^ 2), .eq (a ^ 2) (x ^ 2)])

/-- **The absolute-value template** (template index `14`): `x = X₀`, `a = X₁`. -/
noncomputable def absTemplate : ExPoly := Build.template 2 (absBuild (X 0) (X 1))

/-- The formula of `value.abs` with the variables of the article. -/
noncomputable def absFormula : Formula :=
  .and [.eq (X 1) (X 2 ^ 2 + X 3 ^ 2 + X 4 ^ 2 + X 5 ^ 2), .eq (X 1 ^ 2) (X 0 ^ 2)]

theorem absBuild_run : absBuild (X 0) (X 1) ⟨2, []⟩ = (absFormula, ⟨6, []⟩) := rfl

theorem absTemplate_params : absTemplate.params = 2 := rfl

theorem absTemplate_witnesses : absTemplate.witnesses = 4 := rfl

theorem abs_facts : Build.Facts 2 (absBuild (X 0) (X 1)) 6 [] [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  wp_run (Avail 6 []) 6
  facts_close

theorem absTemplate_wf : absTemplate.WF := abs_facts.wf

/-- The polynomial of `value.abs` is
`((a - z₁² - z₂² - z₃² - z₄²)² + (a² - x²)²)²` (written with `a - (z₁² + ⋯ + z₄²)`). -/
theorem absTemplate_poly : absTemplate.poly =
    ((X 1 - (X 2 ^ 2 + X 3 ^ 2 + X 4 ^ 2 + X 5 ^ 2)) ^ 2 + (X 1 ^ 2 - X 0 ^ 2) ^ 2) ^ 2 := by
  rw [absTemplate, Build.template_poly, Build.fullFormula, absBuild_run, compile_globals_nil]
  simp [absFormula, Formula.compile_and]

/-- **The absolute-value template.** `Rel_{value.abs}(x, a) ⟺ a = |x|`. -/
theorem absTemplate_rel_iff (v : Fin 2 → ℚ) : absTemplate.Rel v ↔ v 1 = |v 0| := by
  unfold absTemplate
  rw [Build.template_rel_iff 2 _ (by rw [absBuild_run]; simp)]
  simp only [absBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and, absFormula,
    Formula.holds_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Formula.holds_eq, map_add, map_pow, ev_X]
  rw [eq_abs_iff_four_squares]
  exact exists_congr fun y => Iff.rfl

/-! ### `value.signed_encode` -/

/-- The construction of `value.signed_encode` on the points `N`, `C`: the points `Q`, `Q₂`,
`Q₊`; the calls `member[N]`, `member[C]`, `natural[Q]`, `raw_add[Q, Q, Q₂]`; and the
disjunction of `⋀(eq(N, Q), eq(C, Q₂))` and
`⋀(raw_add[Q, G, Q₊], eq(N, neg(Q₊)), raw_add[Q₂, G, C])`, where the generator point `G` is
requested (its three constants allocated) just before the first call of the second branch. -/
noncomputable def signedEncodeBuild (I : Constructors E) (cstar ell T : ℤ) (N C : Code) :
    Build Formula := do
  let Q ← Build.point
  let Q2 ← Build.point
  let Qp ← Build.point
  let m1 ← Build.call memberTemplate N
  let m2 ← Build.call memberTemplate C
  let n ← Build.call (naturalTemplate I cstar ell T) Q
  let a ← Build.call rawAddTemplate (Fin.append (Fin.append Q Q) Q2)
  let G ← Build.gen
  let b1 ← Build.call rawAddTemplate (Fin.append (Fin.append Q G) Qp)
  let G' ← Build.gen
  let b2 ← Build.call rawAddTemplate (Fin.append (Fin.append Q2 G') C)
  pure (.and [m1, m2, n, a, .or [.and [peq N Q, peq C Q2], .and [b1, peq N Qp.neg, b2]]])

/-- **The signed-encoding template** (template index `13`): `N = (X₀, …, X₄)`,
`C = (X₅, …, X₉)`. -/
noncomputable def signedEncodeTemplate (I : Constructors E) (cstar ell T : ℤ) : ExPoly :=
  Build.template 10 (signedEncodeBuild I cstar ell T (varPoint 0) (varPoint 5))

/-- The call blocks of `value.signed_encode`, in order. -/
def signedEncodeBlocks : List (ℕ × ℕ) :=
  [(25, 7), (32, 7), (39, 140604), (140643, 6), (140652, 6), (140658, 6)]

/-- The rational constants of `value.signed_encode`. -/
def signedEncodeGlobals : List (ℕ × ℤ × ℤ) :=
  [(140649, 1641, 8), (140650, -15465, 4), (140651, 87483, 32)]

set_option maxRecDepth 20000 in
theorem signedEncode_facts (I : Constructors E) (cstar ell T : ℤ) :
    Build.Facts 10 (signedEncodeBuild I cstar ell T (varPoint 0) (varPoint 5)) 140664
      signedEncodeBlocks signedEncodeGlobals := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := memberTemplate_wf
  have := memberTemplate_witnesses
  have := naturalTemplate_wf I cstar ell T
  have := naturalTemplate_witnesses I cstar ell T
  have := rawAddTemplate_wf
  have := rawAddTemplate_witnesses
  wp_run (Avail 140664 signedEncodeBlocks) 140664
  facts_close

/-- The formula of `value.signed_encode` with the variables of the article: `Q`, `Q₂`, `Q₊` at
`X₁₀`, `X₁₅`, `X₂₀`, the generator point at `X₁₄₀₆₄₉, X₁₄₀₆₅₀, X₁₄₀₆₅₁`. -/
noncomputable def signedEncodeFormula (I : Constructors E) (cstar ell T : ℤ) : Formula :=
  let N := varPoint 0
  let C := varPoint 5
  let Q := varPoint 10
  let Q2 := varPoint 15
  let Qp := varPoint 20
  .and [.call memberTemplate N 25, .call memberTemplate C 32,
    .call (naturalTemplate I cstar ell T) Q 39,
    .call rawAddTemplate (Fin.append (Fin.append Q Q) Q2) 140643,
    .or [.and [peq N Q, peq C Q2],
      .and [.call rawAddTemplate (Fin.append (Fin.append Q (genPoint 140649)) Qp) 140652,
        peq N Qp.neg, .call rawAddTemplate (Fin.append (Fin.append Q2 (genPoint 140649)) C) 140658]]]

theorem signedEncodeBuild_formula (I : Constructors E) (cstar ell T : ℤ) :
    (signedEncodeBuild I cstar ell T (varPoint 0) (varPoint 5) ⟨10, []⟩).1 =
      signedEncodeFormula I cstar ell T := by
  dsimp only [signedEncodeBuild, Build.bind_apply, Build.pure_apply, Build.call, Build.point,
    Build.gen, Build.rational, Build.normalize]
  simp only [memberTemplate_witnesses, naturalTemplate_witnesses, rawAddTemplate_witnesses]
  rfl

theorem signedEncodeTemplate_params (I : Constructors E) (cstar ell T : ℤ) :
    (signedEncodeTemplate I cstar ell T).params = 10 := rfl

theorem signedEncodeTemplate_witnesses (I : Constructors E) (cstar ell T : ℤ) :
    (signedEncodeTemplate I cstar ell T).witnesses = 140654 :=
  (signedEncode_facts I cstar ell T).witnesses

theorem signedEncodeTemplate_wf (I : Constructors E) (cstar ell T : ℤ) :
    (signedEncodeTemplate I cstar ell T).WF := (signedEncode_facts I cstar ell T).wf

/-- The relation of `value.signed_encode` through its private blocks; the generator constants
are outside the internal disjunction. -/
theorem signedEncodeTemplate_rel_iff (I : Constructors E) (cstar ell T : ℤ) (a : Fin 10 → ℚ) :
    (signedEncodeTemplate I cstar ell T).Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 10, y i = a i) ∧
      (y 140649 = 1641 / 8 ∧ y 140650 = -15465 / 4 ∧ y 140651 = 87483 / 32) ∧
      (signedEncodeFormula I cstar ell T).Lift y := by
  unfold signedEncodeTemplate
  rw [(signedEncode_facts I cstar ell T).rel_iff, signedEncodeBuild_formula]
  simp [signedEncodeGlobals]

/-! ### `value.close_coordinates` -/

/-- The construction of `value.close_coordinates` on the points `A`, `L`, `J` and `t`: the
pairs `ζ_A`, `ζ_L`, `ζ_J`, `Div(ζ_J, ζ_A)` with value `q`, the fresh `a₀`, `a₁`, `δ`,
`POS(a₀ + a₁ - δ)`, the calls `member[A]`, `member[L]`, `member[J]`, the gadgets `Z(A, ζ_A)`,
`Z(L, ζ_L)`, `Z(J, ζ_J)`, the calls `value.abs[(ζ_L)₀, a₀]`, `value.abs[(ζ_L)₁, a₁]`,
`NZ(a₀ + a₁)` and `value.abs[t - q₀, δ]`. -/
noncomputable def closeBuild (A L J : Code) (t : Poly) : Build Formula := do
  let za ← Build.freshPair
  let zl ← Build.freshPair
  let zj ← Build.freshPair
  let ⟨q, fr⟩ ← Build.fdiv zj za
  let a0 ← Build.fresh
  let a1 ← Build.fresh
  let δ ← Build.fresh
  let fp ← Build.pos (a0 + a1 - δ)
  let m1 ← Build.call memberTemplate A
  let m2 ← Build.call memberTemplate L
  let m3 ← Build.call memberTemplate J
  let zA ← Build.zGadget A za
  let zL ← Build.zGadget L zl
  let zJ ← Build.zGadget J zj
  let c1 ← Build.call absTemplate ![zl.1, a0]
  let c2 ← Build.call absTemplate ![zl.2, a1]
  let ne ← Build.nz (a0 + a1)
  let c3 ← Build.call absTemplate ![t - q.1, δ]
  pure (.and [m1, m2, m3, fin A, fin L, zA, zL, zJ, fr, c1, c2, ne, c3, fp])

/-- **The coordinate-window template** (template index `15`): `A`, `L`, `J` the points at
`X₀`, `X₅`, `X₁₀` and `t = X₁₅`. -/
noncomputable def closeTemplate : ExPoly :=
  Build.template 16 (closeBuild (varPoint 0) (varPoint 5) (varPoint 10) (X 15))

/-- The call blocks of `value.close_coordinates`, in order. -/
def closeBlocks : List (ℕ × ℕ) := [(32, 7), (39, 7), (46, 7), (56, 4), (60, 4), (65, 4)]

theorem close_facts :
    Build.Facts 16 (closeBuild (varPoint 0) (varPoint 5) (varPoint 10) (X 15)) 69 closeBlocks [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := memberTemplate_wf
  have := memberTemplate_witnesses
  have := absTemplate_wf
  have := absTemplate_witnesses
  wp_run (Avail 69 closeBlocks) 69
  facts_close

/-- The formula of `value.close_coordinates` with the variables of the article. -/
noncomputable def closeFormula : Formula :=
  let A := varPoint 0
  let L := varPoint 5
  let J := varPoint 10
  let zA := varPair 16
  let zL := varPair 18
  let zJ := varPair 20
  .and [.call memberTemplate A 32, .call memberTemplate L 39, .call memberTemplate J 46, fin A,
    fin L, zFormula A zA 53, zFormula L zL 54, zFormula J zJ 55, divFormula zJ zA (varPair 22) 24,
    .call absTemplate ![zL.1, X 25] 56, .call absTemplate ![zL.2, X 26] 60,
    nzFormula (X 25 + X 26) 64, .call absTemplate ![X 15 - X 22, X 27] 65,
    posFormula (X 25 + X 26 - X 27) 28]

theorem closeBuild_formula :
    (closeBuild (varPoint 0) (varPoint 5) (varPoint 10) (X 15) ⟨16, []⟩).1 = closeFormula := by
  dsimp only [closeBuild, Build.bind_apply, Build.pure_apply, Build.call, Build.freshPair,
    Build.fresh, Build.fdiv, Build.fnz, Build.nz, Build.pos, Build.zGadget]
  simp only [memberTemplate_witnesses, absTemplate_witnesses]
  rfl

theorem closeTemplate_params : closeTemplate.params = 16 := rfl

theorem closeTemplate_witnesses : closeTemplate.witnesses = 53 := close_facts.witnesses

theorem closeTemplate_wf : closeTemplate.WF := close_facts.wf

/-- The relation of `value.close_coordinates` through its private blocks. -/
theorem closeTemplate_rel_iff (a : Fin 16 → ℚ) :
    closeTemplate.Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 16, y i = a i) ∧ closeFormula.Lift y := by
  unfold closeTemplate
  rw [← closeBuild_formula]
  exact close_facts.rel_iff_nil a

/-! ### `value.test` -/

/-- The contact product `F = (t-0)(t-(-15))(t-(-20))(t-(-24))(t-(-30))(t-(-60))` of the value
test. -/
noncomputable def valueContact (t : Poly) : Poly :=
  (t - 0) * (t - (-15)) * (t - (-20)) * (t - (-24)) * (t - (-30)) * (t - (-60))

/-- One local test of `value.test` at the point `P`: the pairs `w`, `ζ`, and the formulas
`IX(P, w)` and `Z(P, ζ)`. -/
noncomputable def valueLocal (P : Code) : Build (Pair × Pair × List Formula) := do
  let w ← Build.freshPair
  let z ← Build.freshPair
  let g ← Build.zGadget P z
  pure (w, z, [ixFormula P w, g])

/-- The construction of `value.test` on the points `N`, `K` and `t`, following
`addVariableShiftTemplates` (`value.test`). -/
noncomputable def valueTestBuild (I : Constructors E) (cstar ell T : ℤ) (N K : Code) (t : Poly) :
    Build Formula := do
  let C1 ← Build.point
  let H ← Build.point
  let U ← Build.point
  let V0 ← Build.point
  let V1 ← Build.point
  let m0 ← Build.call memberTemplate N
  let m1 ← Build.call memberTemplate K
  let m2 ← Build.call memberTemplate C1
  let m3 ← Build.call memberTemplate H
  let m4 ← Build.call memberTemplate U
  let m5 ← Build.call memberTemplate V0
  let m6 ← Build.call memberTemplate V1
  let mu ← Build.call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append K N) C1)
  let s0 ← Build.call rawAddTemplate (Fin.append (Fin.append H K.neg) V0)
  let s1 ← Build.call rawAddTemplate (Fin.append (Fin.append U C1.neg) V1)
  let ⟨w0, z0, l0⟩ ← valueLocal H
  let ⟨w1, z1, l1⟩ ← valueLocal U
  let ⟨w2, z2, l2⟩ ← valueLocal V0
  let ⟨w3, z3, l3⟩ ← valueLocal V1
  let ⟨ρ0, d0⟩ ← Build.fdiv z1 z0
  let ⟨ρ1, d1⟩ ← Build.fdiv z3 z2
  let F := valueContact t
  let eta ← Build.fresh
  let q ← Build.fresh
  let R0 ← Build.fresh
  let a0 ← Build.fresh
  let R ← Build.fresh
  let nF ← Build.nz F
  let na ← Build.nz a0
  let Cn ← Build.freshPairs 6
  let ⟨ω, dW⟩ ← Build.fdiv Pair.one (slopeW R (List.ofFn Cn))
  let Θ ← Build.fresh
  let B ← Build.fresh
  let nΘ ← Build.nz Θ
  let cp ← Build.call poleTemplate ![B]
  pure (.and ([m0, m1, m2, m3, m4, m5, m6, fin K, mu, s0, s1, fin H, fin V0] ++
    l0 ++ l1 ++ l2 ++ l3 ++ [d0, d1] ++
    [nF, .eq (eta ^ 2) 1, .eq R0 (eta * C (2730 ^ 6) * F), .eq a0 (1 - R0 * q ^ 2), na,
      .eq R (R0 * a0 ^ 2)] ++
    [feq (Pair.smul F (Cn 0)) w0, feq (Pair.smul F (Cn 1)) w1, feq (Pair.smul F (Cn 2)) w2.conj,
      feq (Pair.smul F (Cn 3)) w3.conj, feq (Pair.smul F (Cn 4)) (ρ0.sub (t, 0)),
      feq (Pair.smul F (Cn 5)) (ρ1.conj.sub (t, 0))] ++
    [dW, .eq Θ (2 * ω.1), nΘ, .eq (B * Θ ^ 2) R, cp]))

/-- **The value-test template** (template index `16`): `N = (X₀, …, X₄)`, `K = (X₅, …, X₉)`,
`t = X₁₀`. -/
noncomputable def valueTestTemplate (I : Constructors E) (cstar ell T : ℤ) : ExPoly :=
  Build.template 11 (valueTestBuild I cstar ell T (varPoint 0) (varPoint 5) (X 10))

/-- The call blocks of `value.test`, in order. -/
def valueTestBlocks : List (ℕ × ℕ) :=
  [(36, 7), (43, 7), (50, 7), (57, 7), (64, 7), (71, 7), (78, 7), (85, 35134), (35219, 6),
    (35225, 6), (35282, 11)]

set_option maxRecDepth 20000 in
theorem valueTest_facts (I : Constructors E) (cstar ell T : ℤ) :
    Build.Facts 11 (valueTestBuild I cstar ell T (varPoint 0) (varPoint 5) (X 10)) 35293
      valueTestBlocks [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := memberTemplate_wf
  have := memberTemplate_witnesses
  have := multiplyTemplate_wf I cstar ell T
  have := multiplyTemplate_witnesses I cstar ell T
  have := rawAddTemplate_wf
  have := rawAddTemplate_witnesses
  have := poleTemplate_wf
  have := poleTemplate_witnesses
  have hW := @PairIn.slopeW (Avail 35293 valueTestBlocks)
  wp_run (Avail 35293 valueTestBlocks) 35293
  facts_close

/-- The local test of `value.test` at the point `P` with base `b`: `IX(P, w)` and `Z(P, ζ)` with
`w = (X_b, X_{b+1})`, `ζ = (X_{b+2}, X_{b+3})` and inverse witness `X_{b+4}`. -/
noncomputable def valueLocalFormula (P : Code) (b : ℕ) : List Formula :=
  [ixFormula P (varPair b), zFormula P (varPair (b + 2)) (b + 4)]

/-- The formula of `value.test` with the variables of the article. -/
noncomputable def valueTestFormula (I : Constructors E) (cstar ell T : ℤ) : Formula :=
  let N := varPoint 0
  let K := varPoint 5
  let t := X 10
  let C1 := varPoint 11
  let H := varPoint 16
  let U := varPoint 21
  let V0 := varPoint 26
  let V1 := varPoint 31
  let F := valueContact t
  let eta := X 35257
  let R0 := X 35259
  let a0 := X 35260
  let R := X 35261
  let Cn : Fin 6 → Pair := fun j => varPair (35264 + 2 * j)
  .and ([.call memberTemplate N 36, .call memberTemplate K 43, .call memberTemplate C1 50,
      .call memberTemplate H 57, .call memberTemplate U 64, .call memberTemplate V0 71,
      .call memberTemplate V1 78, fin K,
      .call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append K N) C1) 85,
      .call rawAddTemplate (Fin.append (Fin.append H K.neg) V0) 35219,
      .call rawAddTemplate (Fin.append (Fin.append U C1.neg) V1) 35225, fin H, fin V0] ++
    valueLocalFormula H 35231 ++ valueLocalFormula U 35236 ++ valueLocalFormula V0 35241 ++
    valueLocalFormula V1 35246 ++
    [divFormula (varPair 35238) (varPair 35233) (varPair 35251) 35253,
      divFormula (varPair 35248) (varPair 35243) (varPair 35254) 35256] ++
    [nzFormula F 35262, .eq (eta ^ 2) 1, .eq R0 (eta * C (2730 ^ 6) * F),
      .eq a0 (1 - R0 * X 35258 ^ 2), nzFormula a0 35263, .eq R (R0 * a0 ^ 2)] ++
    [feq (Pair.smul F (Cn 0)) (varPair 35231), feq (Pair.smul F (Cn 1)) (varPair 35236),
      feq (Pair.smul F (Cn 2)) (varPair 35241).conj, feq (Pair.smul F (Cn 3)) (varPair 35246).conj,
      feq (Pair.smul F (Cn 4)) ((varPair 35251).sub (t, 0)),
      feq (Pair.smul F (Cn 5)) ((varPair 35254).conj.sub (t, 0))] ++
    [divFormula Pair.one (slopeW R (List.ofFn Cn)) (varPair 35276) 35278,
      .eq (X 35279) (2 * X 35276), nzFormula (X 35279) 35281, .eq (X 35280 * X 35279 ^ 2) R,
      .call poleTemplate ![X 35280] 35282])

theorem valueTestBuild_formula (I : Constructors E) (cstar ell T : ℤ) :
    (valueTestBuild I cstar ell T (varPoint 0) (varPoint 5) (X 10) ⟨11, []⟩).1 =
      valueTestFormula I cstar ell T := by
  dsimp only [valueTestBuild, valueLocal, Build.bind_apply, Build.pure_apply, Build.call,
    Build.point, Build.freshPair, Build.freshPairs, Build.fresh, Build.fdiv, Build.fnz, Build.nz,
    Build.zGadget]
  simp only [memberTemplate_witnesses, multiplyTemplate_witnesses, rawAddTemplate_witnesses]
  rfl

theorem valueTestTemplate_params (I : Constructors E) (cstar ell T : ℤ) :
    (valueTestTemplate I cstar ell T).params = 11 := rfl

theorem valueTestTemplate_witnesses (I : Constructors E) (cstar ell T : ℤ) :
    (valueTestTemplate I cstar ell T).witnesses = 35282 :=
  (valueTest_facts I cstar ell T).witnesses

theorem valueTestTemplate_wf (I : Constructors E) (cstar ell T : ℤ) :
    (valueTestTemplate I cstar ell T).WF := (valueTest_facts I cstar ell T).wf

/-- The relation of `value.test` through its private blocks. -/
theorem valueTestTemplate_rel_iff (I : Constructors E) (cstar ell T : ℤ) (a : Fin 11 → ℚ) :
    (valueTestTemplate I cstar ell T).Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 11, y i = a i) ∧
      (valueTestFormula I cstar ell T).Lift y := by
  unfold valueTestTemplate
  rw [← valueTestBuild_formula]
  exact (valueTest_facts I cstar ell T).rel_iff_nil a

theorem pow_six_2730 : (2730 : ℤ) ^ 6 = 413976684737889000000 := by
  norm_num

/-! ### `value.exceptions` -/

/-- The binary digits of `k`, least significant first (`fuel` bounds the number of digits). -/
def binDigitsAux : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, k => if k = 0 then [] else (k % 2 == 1) :: binDigitsAux fuel (k / 2)

/-- The binary digits of `k`, least significant first. -/
def binDigits (k : ℕ) : List Bool := binDigitsAux k k

/-- The double-and-add chain of `fixedMultiple` on the binary digits of `k`: with current
value `out` and base `base`, for each digit, if it is `1` take a fresh point `σ` and call
`raw_add[out, base, σ]`; if digits remain, take a fresh point `δ` and call
`raw_add[base, base, δ]`. The value is the final `out`. -/
noncomputable def chainBuild (out base : Code) : List Bool → Build (Code × List Formula)
  | [] => pure (out, [])
  | d :: ds => do
    let ⟨out', fs⟩ ← (match d with
      | true => do
        let σ ← Build.point
        let f ← Build.call rawAddTemplate (Fin.append (Fin.append out base) σ)
        pure (σ, [f])
      | false => pure (out, []) : Build (Code × List Formula))
    match ds with
    | [] => pure (out', fs)
    | d' :: ds' => do
      let δ ← Build.point
      let f ← Build.call rawAddTemplate (Fin.append (Fin.append base base) δ)
      let ⟨v, gs⟩ ← chainBuild out' δ (d' :: ds')
      pure (v, fs ++ [f] ++ gs)

/-- `fixedMultiple(p, c)`: the chain for `|c|` on `p` (for `c ≥ 0`) or on `neg(p)` (for
`c < 0`), started at `O`. -/
noncomputable def fixedMultipleBuild (p : Code) (c : ℤ) : Build (Code × List Formula) :=
  chainBuild Code.O (if c < 0 then p.neg else p) (binDigits c.natAbs)

/-- The branch `β_c = ⋀(chain formula, eq(N, chain value), t ≐ c)` of `value.exceptions`. -/
noncomputable def exceptionBranch (N : Code) (t : Poly) (c : ℤ) : Build Formula := do
  let G ← Build.gen
  let ⟨v, fs⟩ ← fixedMultipleBuild G c
  pure (.and [.and fs, peq N v, .eq t (C c)])

/-- The construction of `value.exceptions` on the point `N` and `t`: the six branches for
`c = 0, -15, -20, -24, -30, -60` in this order, then the call `member[N]`. -/
noncomputable def exceptionsBuild (N : Code) (t : Poly) : Build Formula := do
  let b0 ← exceptionBranch N t 0
  let b1 ← exceptionBranch N t (-15)
  let b2 ← exceptionBranch N t (-20)
  let b3 ← exceptionBranch N t (-24)
  let b4 ← exceptionBranch N t (-30)
  let b5 ← exceptionBranch N t (-60)
  let m ← Build.call memberTemplate N
  pure (.and [m, .or [b0, b1, b2, b3, b4, b5]])

/-- **The exceptional-values template** (template index `17`): `N = (X₀, …, X₄)`, `t = X₅`. -/
noncomputable def exceptionsTemplate : ExPoly := Build.template 6 (exceptionsBuild (varPoint 0) (X 5))

/-- The call blocks of `value.exceptions` in formula order: `member` (allocated last), then the
36 raw additions of the chains (allocated in this order). -/
def exceptionsBlocks : List (ℕ × ℕ) :=
  (405, 7) :: (List.range 36).map (fun i => (14 + 11 * i, 6))

/-- The rational constants of `value.exceptions`. -/
def exceptionsGlobals : List (ℕ × ℤ × ℤ) := [(6, 1641, 8), (7, -15465, 4), (8, 87483, 32)]

theorem binDigits_contacts : binDigits 0 = [] ∧ binDigits 15 = [true, true, true, true] ∧
    binDigits 20 = [false, false, true, false, true] ∧
    binDigits 24 = [false, false, false, true, true] ∧
    binDigits 30 = [false, true, true, true, true] ∧
    binDigits 60 = [false, false, true, true, true, true] := by
  decide

set_option maxRecDepth 20000 in
theorem exceptions_facts :
    Build.Facts 6 (exceptionsBuild (varPoint 0) (X 5)) 412 exceptionsBlocks exceptionsGlobals := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := memberTemplate_wf
  have := memberTemplate_witnesses
  have := rawAddTemplate_wf
  have := rawAddTemplate_witnesses
  obtain ⟨h0, h15, h20, h24, h30, h60⟩ := binDigits_contacts
  simp only [exceptionsBuild, exceptionBranch, fixedMultipleBuild, Int.natAbs_neg,
    show ((0 : ℤ) < 0) = False by decide, show ((-15 : ℤ) < 0) = True by decide,
    show ((-20 : ℤ) < 0) = True by decide, show ((-24 : ℤ) < 0) = True by decide,
    show ((-30 : ℤ) < 0) = True by decide, show ((-60 : ℤ) < 0) = True by decide,
    ite_true, ite_false, show (0 : ℤ).natAbs = 0 from rfl, show (15 : ℤ).natAbs = 15 from rfl,
    show (20 : ℤ).natAbs = 20 from rfl, show (24 : ℤ).natAbs = 24 from rfl,
    show (30 : ℤ).natAbs = 30 from rfl, show (60 : ℤ).natAbs = 60 from rfl, h0, h15, h20, h24,
    h30, h60]
  wp_run (Avail 412 exceptionsBlocks) 412
  facts_close

theorem exceptionsTemplate_params : exceptionsTemplate.params = 6 := rfl

theorem exceptionsTemplate_witnesses : exceptionsTemplate.witnesses = 406 :=
  exceptions_facts.witnesses

theorem exceptionsTemplate_wf : exceptionsTemplate.WF := exceptions_facts.wf

/-- The relation of `value.exceptions` through its private blocks; the generator constants
are outside the disjunction. -/
theorem exceptionsTemplate_rel_iff (a : Fin 6 → ℚ) :
    exceptionsTemplate.Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 6, y i = a i) ∧
      (y 6 = 1641 / 8 ∧ y 7 = -15465 / 4 ∧ y 8 = 87483 / 32) ∧
      (exceptionsBuild (varPoint 0) (X 5) ⟨6, []⟩).1.Lift y := by
  unfold exceptionsTemplate
  rw [exceptions_facts.rel_iff]
  simp [exceptionsGlobals]

end ZInQ.Syntax
