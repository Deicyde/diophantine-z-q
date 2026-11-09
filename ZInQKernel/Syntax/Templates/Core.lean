import ZInQKernel.Syntax.Templates.Member
import ZInQKernel.Hypotheses.Pole

/-!
# The local templates of the multiplication certificate

Templates `2` (`raw_z`), `3` (`raw_inverse_x`), `4` (`log25`) and `5` (`pole`) of the
library, from `addCore` in `construction/multiplication-certificate.js` (the gadgets
`EllipticCore.z`, `EllipticCore.inverseX` and `EllipticCore.log25` of
`construction/rational-elliptic-core.js`). None has rational constants, so each polynomial is
`κ(φ)²`.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-! ### `raw_z` -/

/-- The construction of `raw_z` on the point `p` and the pair `ζ`: the gadget `Z(p, ζ)`. -/
noncomputable def rawZBuild (p : Code) (ζ : Pair) : Build Formula := Build.zGadget p ζ

/-- **The local parameter template** (template index `2`). -/
noncomputable def rawZTemplate : ExPoly := Build.template 7 (rawZBuild (varPoint 0) (varPair 5))

theorem rawZBuild_run :
    rawZBuild (varPoint 0) (varPair 5) ⟨7, []⟩ = (zFormula (varPoint 0) (varPair 5) 7, ⟨8, []⟩) :=
  rfl

theorem rawZTemplate_params : rawZTemplate.params = 7 := rfl

theorem rawZTemplate_witnesses : rawZTemplate.witnesses = 1 := rfl

theorem rawZTemplate_wf : rawZTemplate.WF := by
  refine Build.template_wf_of_fok 7 _ (G := Avail 8 []) (fun i h => h.1) (by decide)
    (by decide) ?_
  show Build.WP (rawZBuild (varPoint 0) (varPair 5)) ⟨7, []⟩ fun φ _ => FOk (Avail 8 []) 8 φ
  wp_run (Avail 8 []) 8
  scope

/-- The polynomial of `raw_z` is `κ(Z(p, ζ))²`. -/
theorem rawZTemplate_poly :
    rawZTemplate.poly = (zFormula (varPoint 0) (varPair 5) 7).compile ^ 2 := by
  rw [rawZTemplate, Build.template_poly, Build.fullFormula, rawZBuild_run]
  exact compile_globals_nil _

theorem rawZTemplate_rel_iff (a : Fin 7 → ℚ) :
    rawZTemplate.Rel a ↔ ∃ y : Fin 1 → ℚ,
      (zFormula (varPoint 0) (varPair 5) 7).Holds (assign 7 1 a y) := by
  unfold rawZTemplate
  rw [Build.template_rel_iff 7 _ (by rw [rawZBuild_run]; simp)]
  simp only [rawZBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and]

/-! ### `raw_inverse_x` -/

/-- The construction of `raw_inverse_x` on the point `p` and the pair `v`: the formula
`IX(p, v)`. -/
noncomputable def rawInverseXBuild (p : Code) (v : Pair) : Build Formula := pure (ixFormula p v)

/-- **The inverse abscissa template** (template index `3`). -/
noncomputable def rawInverseXTemplate : ExPoly :=
  Build.template 7 (rawInverseXBuild (varPoint 0) (varPair 5))

theorem rawInverseXBuild_run :
    rawInverseXBuild (varPoint 0) (varPair 5) ⟨7, []⟩ =
      (ixFormula (varPoint 0) (varPair 5), ⟨7, []⟩) := rfl

theorem rawInverseXTemplate_params : rawInverseXTemplate.params = 7 := rfl

theorem rawInverseXTemplate_witnesses : rawInverseXTemplate.witnesses = 0 := rfl

theorem rawInverseXTemplate_wf : rawInverseXTemplate.WF := by
  refine Build.template_wf_of_fok 7 _ (G := Avail 7 []) (fun i h => h.1) (by decide)
    (by decide) ?_
  show Build.WP (rawInverseXBuild (varPoint 0) (varPair 5)) ⟨7, []⟩
    fun φ _ => FOk (Avail 7 []) 7 φ
  wp_run (Avail 7 []) 7
  scope

/-- The polynomial of `raw_inverse_x` is `κ(IX(p, v))²`. -/
theorem rawInverseXTemplate_poly :
    rawInverseXTemplate.poly = (ixFormula (varPoint 0) (varPair 5)).compile ^ 2 := by
  rw [rawInverseXTemplate, Build.template_poly, Build.fullFormula, rawInverseXBuild_run]
  exact compile_globals_nil _

theorem rawInverseXTemplate_rel_iff (a : Fin 7 → ℚ) :
    rawInverseXTemplate.Rel a ↔ ∃ y : Fin 0 → ℚ,
      (ixFormula (varPoint 0) (varPair 5)).Holds (assign 7 0 a y) := by
  unfold rawInverseXTemplate
  rw [Build.template_rel_iff 7 _ (by rw [rawInverseXBuild_run]; simp)]
  simp only [rawInverseXBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and]

/-- The values of the parameter point and pair of `raw_z` and `raw_inverse_x` at
`assign 7 m a y`. -/
theorem evCode_assign_varPoint_zero {m : ℕ} (a : Fin 7 → ℚ) (y : Fin m → ℚ) :
    evCode (assign 7 m a y) (varPoint 0) = fun i => a (Fin.castLE (by omega) i) := by
  funext i
  simp only [evCode, ev_varPoint, zero_add]
  exact assign_of_lt a y (by omega)

theorem val_assign_varPair_five {m : ℕ} (a : Fin 7 → ℚ) (y : Fin m → ℚ) :
    Pair.val (assign 7 m a y) (varPair 5) = ⟨a 5, a 6⟩ := by
  ext
  · simp only [Pair.re_val, ev_varPair_fst]; exact assign_of_lt (i := 5) a y (by omega)
  · simp only [Pair.im_val, ev_varPair_snd]; exact assign_of_lt (i := 6) a y (by omega)

theorem val_assign_varPoint_x {m : ℕ} (a : Fin 7 → ℚ) (y : Fin m → ℚ) :
    Pair.val (assign 7 m a y) (varPoint 0).x = ⟨a 1, a 2⟩ := by
  ext
  · simp only [Pair.re_val, Code.x, varPoint, ev_X]; exact assign_of_lt (i := 1) a y (by omega)
  · simp only [Pair.im_val, Code.x, varPoint, ev_X]; exact assign_of_lt (i := 2) a y (by omega)

theorem val_assign_varPoint_y {m : ℕ} (a : Fin 7 → ℚ) (y : Fin m → ℚ) :
    Pair.val (assign 7 m a y) (varPoint 0).y = ⟨a 3, a 4⟩ := by
  ext
  · simp only [Pair.re_val, Code.y, varPoint, ev_X]; exact assign_of_lt (i := 3) a y (by omega)
  · simp only [Pair.im_val, Code.y, varPoint, ev_X]; exact assign_of_lt (i := 4) a y (by omega)

/-- **The inverse abscissa template in field terms.** `Rel(p, v)` holds exactly when either
`p = O` and `v = 0`, or `p₀ = 0` and `x(p) · v = 1` in `K₀`. -/
theorem rawInverseXTemplate_rel_iff_field (a : Fin 7 → ℚ) :
    rawInverseXTemplate.Rel a ↔
      ((fun i : Fin 5 => a (Fin.castLE (by omega) i)) = ![1, 0, 0, 0, 0] ∧
          (⟨a 5, a 6⟩ : K0) = 0) ∨
        (a 0 = 0 ∧ (⟨a 1, a 2⟩ : K0) * ⟨a 5, a 6⟩ = 1) := by
  rw [rawInverseXTemplate_rel_iff]
  have h0 : ∀ y : Fin 0 → ℚ, ev (assign 7 0 a y) (varPoint 0 0) = a 0 := fun y => by
    simpa using assign_of_lt a y (show 0 < 7 by omega)
  simp only [holds_ixFormula, evCode_assign_varPoint_zero, val_assign_varPair_five,
    val_assign_varPoint_x, h0]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Fin.elim0, h⟩⟩

/-- **The local parameter template in field terms.** `Rel(p, ζ)` holds exactly when either
`p = O` and `ζ = 0`, or `p₀ = 0`, `y(p) ≠ 0` and `ζ = -x(p)/y(p)` in `K₀`. -/
theorem rawZTemplate_rel_iff_field (a : Fin 7 → ℚ) :
    rawZTemplate.Rel a ↔
      ((fun i : Fin 5 => a (Fin.castLE (by omega) i)) = ![1, 0, 0, 0, 0] ∧
          (⟨a 5, a 6⟩ : K0) = 0) ∨
        (a 0 = 0 ∧ (⟨a 3, a 4⟩ : K0) ≠ 0 ∧
          (⟨a 5, a 6⟩ : K0) = -(⟨a 1, a 2⟩ : K0) / ⟨a 3, a 4⟩) := by
  rw [rawZTemplate_rel_iff]
  have h0 : ∀ y : Fin 1 → ℚ, ev (assign 7 1 a y) (varPoint 0 0) = a 0 := fun y => by
    simpa using assign_of_lt a y (show 0 < 7 by omega)
  have h7 : ∀ y : Fin 1 → ℚ, assign 7 1 a y 7 = y 0 := fun y => assign_add 7 1 a y 0
  have hnorm : ∀ y : Fin 1 → ℚ, ev (assign 7 1 a y) (varPoint 0).y.norm = a 3 ^ 2 - 2 * a 4 ^ 2 :=
    fun y => by
      rw [Pair.ev_norm]
      have := val_assign_varPoint_y a y
      rw [QuadraticAlgebra.ext_iff] at this
      exact congrArg₂ (fun u v => u ^ 2 - 2 * v ^ 2) this.1 this.2
  simp only [holds_zFormula, holds_nzFormula, holds_isO, evCode_assign_varPoint_zero,
    val_assign_varPair_five, val_assign_varPoint_x, val_assign_varPoint_y, h0, h7, hnorm]
  constructor
  · rintro ⟨y, h | ⟨ha, hw, hζ⟩⟩
    · exact Or.inl h
    · have hy : (⟨a 3, a 4⟩ : K0) ≠ 0 :=
        (exists_mul_pairNorm_eq_one_iff (a 3) (a 4)).1 ⟨y 0, hw⟩
      refine Or.inr ⟨ha, hy, ?_⟩
      rw [eq_div_iff hy, mul_comm, hζ]
  · rintro (h | ⟨ha, hy, hζ⟩)
    · exact ⟨fun _ => 0, Or.inl h⟩
    · obtain ⟨w, hw⟩ := (exists_mul_pairNorm_eq_one_iff (a 3) (a 4)).2 hy
      refine ⟨fun _ => w, Or.inr ⟨ha, hw, ?_⟩⟩
      rw [hζ, mul_div_cancel₀ _ hy]

/-! ### `log25` -/

/-- The seven coefficients `c_j = 16575 (-1)^j binom(2j, j)/(4j + 1)` of the truncated
logarithm. -/
def log25Coeffs : List ℤ := [16575, -6630, 11050, -25500, 68250, -198900, 612612]

/-- The loop of `EllipticCore.log25`: with accumulator `out`, the power `δ^j` and the index
`j`, add `c_j (δ^j · ζ^{4j+1})` and multiply the power by `δ`. -/
noncomputable def Pair.log25Aux (ζ : Pair) : List ℤ → Pair → Pair → ℕ → Pair
  | [], out, _, _ => out
  | c :: cs, out, dPower, j =>
    Pair.log25Aux ζ cs (out.add (Pair.smul (C c) (dPower.mul (ζ.pow (4 * j + 1)))))
      (dPower.mul Pair.delta) (j + 1)

/-- `L(ζ) = Σ_{j=0}^{6} c_j (δ^j · ζ^{4j+1})` in pair arithmetic, `δ = (11243, -7950)`. -/
noncomputable def Pair.log25 (ζ : Pair) : Pair := Pair.log25Aux ζ log25Coeffs Pair.zero Pair.one 0

theorem PairIn.log25Aux {G : ℕ → Prop} {ζ : Pair} (hζ : PairIn ζ G) (cs : List ℤ) :
    ∀ {out dPower : Pair} (j : ℕ), PairIn out G → PairIn dPower G →
      PairIn (Pair.log25Aux ζ cs out dPower j) G := by
  induction cs with
  | nil => intro out dPower j hout _; exact hout
  | cons c cs ih =>
    intro out dPower j hout hd
    exact ih (j + 1) (hout.add ((PairIn.smul (VarsIn.C c G)) (hd.mul (hζ.pow _))))
      (hd.mul PairIn.delta)

theorem PairIn.log25 {G : ℕ → Prop} {ζ : Pair} (hζ : PairIn ζ G) : PairIn ζ.log25 G :=
  PairIn.log25Aux hζ _ 0 PairIn.zero PairIn.one

/-- The construction of `log25` on the pairs `ζ`, `λ`: the pair equation `L(ζ) ≐ λ`. -/
noncomputable def log25Build (ζ lam : Pair) : Build Formula := pure (feq ζ.log25 lam)

/-- **The truncated logarithm template** (template index `4`). -/
noncomputable def log25Template : ExPoly := Build.template 4 (log25Build (varPair 0) (varPair 2))

theorem log25Build_run :
    log25Build (varPair 0) (varPair 2) ⟨4, []⟩ = (feq (varPair 0).log25 (varPair 2), ⟨4, []⟩) :=
  rfl

theorem log25Template_params : log25Template.params = 4 := rfl

theorem log25Template_witnesses : log25Template.witnesses = 0 := rfl

theorem log25Template_wf : log25Template.WF := by
  refine Build.template_wf_of_fok 4 _ (G := Avail 4 []) (fun i h => h.1) (by decide)
    (by decide) ?_
  show FOk (Avail 4 []) 4 (feq (varPair 0).log25 (varPair 2))
  exact FOk.feq (PairIn.log25 (PairIn.varPair (by decide) (by decide)))
    (PairIn.varPair (by decide) (by decide))

/-- The polynomial of `log25` is `((L₀(ζ) - λ₀)² + (L₁(ζ) - λ₁)²)²`. -/
theorem log25Template_poly :
    log25Template.poly =
      (((varPair 0).log25.1 - X 2) ^ 2 + ((varPair 0).log25.2 - X 3) ^ 2) ^ 2 := by
  rw [log25Template, Build.template_poly, Build.fullFormula, log25Build_run,
    compile_globals_nil]
  simp [feq, Formula.compile_and, varPair]

theorem log25Template_rel_iff (a : Fin 4 → ℚ) :
    log25Template.Rel a ↔ ∃ y : Fin 0 → ℚ,
      (feq (varPair 0).log25 (varPair 2)).Holds (assign 4 0 a y) := by
  unfold log25Template
  rw [Build.template_rel_iff 4 _ (by rw [log25Build_run]; simp)]
  simp only [log25Build_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and]

/-! ### `pole` -/

/-- The factor `m = (1-2b₀)(1+b₁)(1+2b₂)(1+4b₃)(1+6b₄)(1+12b₅)` of the pole polynomial. -/
noncomputable def poleM (b : Fin 6 → Poly) : Poly :=
  (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) * (1 + 12 * b 5)

/-- `H = A(A - B²)`. -/
noncomputable def poleH (A B : Poly) : Poly := A * (A - B ^ 2)

/-- `T₁ = A(A - e)(A + e)` (Route K; the manuscript has `A + 3e`). -/
noncomputable def poleT1 (A e : Poly) : Poly := A * (A - e) * (A + e)

/-- `T₂ = A(Az² - eH)(Az² + eH)` (Route K; the manuscript has `Az² + 3eH`). -/
noncomputable def poleT2 (A e z H : Poly) : Poly := A * (A * z ^ 2 - e * H) * (A * z ^ 2 + e * H)

/-- `B S` with `A` given: `S = Σ(bᵢ² - bᵢ)² + (eHzw - 1)² + (r₁² - T₁)² + (r₂² - T₂)²`. -/
noncomputable def poleBS (B A : Poly) (b : Fin 6 → Poly) (e z r1 r2 w : Poly) : Poly :=
  B * ((b 0 ^ 2 - b 0) ^ 2 + (b 1 ^ 2 - b 1) ^ 2 + (b 2 ^ 2 - b 2) ^ 2 + (b 3 ^ 2 - b 3) ^ 2 +
    (b 4 ^ 2 - b 4) ^ 2 + (b 5 ^ 2 - b 5) ^ 2 + (e * poleH A B * z * w - 1) ^ 2 +
    (r1 ^ 2 - poleT1 A e) ^ 2 + (r2 ^ 2 - poleT2 A e z (poleH A B)) ^ 2)

/-- The pole polynomial `Q_pole = B S` at polynomials `B`, `b₀, …, b₅`, `e`, `z`, `r₁`, `r₂`,
`w`, with `m = (1-2b₀)(1+b₁)(1+2b₂)(1+4b₃)(1+6b₄)(1+12b₅)`, `A = mB`, `H = A(A - B²)`,
`T₁ = A(A-e)(A+e)`, `T₂ = A(Az²-eH)(Az²+eH)` (the Route K polynomial `ZInQ.polePoly`) and
`S = Σ(bᵢ² - bᵢ)² + (eHzw - 1)² + (r₁² - T₁)² + (r₂² - T₂)²`. -/
noncomputable def polePolyOf (B : Poly) (b : Fin 6 → Poly) (e z r1 r2 w : Poly) : Poly :=
  poleBS B (poleM b * B) b e z r1 r2 w

theorem VarsIn.polePoly {G : ℕ → Prop} {B e z r1 r2 w : Poly} {b : Fin 6 → Poly}
    (hB : VarsIn B G) (hb : ArgsIn b G) (he : VarsIn e G) (hz : VarsIn z G)
    (hr1 : VarsIn r1 G) (hr2 : VarsIn r2 G) (hw : VarsIn w G) :
    VarsIn (polePolyOf B b e z r1 r2 w) G := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  have h5 := hb 5
  have hA : VarsIn (poleM b * B) G := by unfold poleM; scope
  have hH : VarsIn (poleH (poleM b * B) B) G := by unfold poleH; scope
  unfold polePolyOf poleBS
  generalize poleM b * B = A at hA hH ⊢
  unfold poleT1 poleT2
  scope

/-- The construction of `pole` on the input `B`: the six bits, then `e`, `z`, `r₁`, `r₂`, `w`,
and the atom `B S ≐ 0`. -/
noncomputable def poleBuild (B : Poly) : Build Formula := do
  let b0 ← Build.fresh
  let b1 ← Build.fresh
  let b2 ← Build.fresh
  let b3 ← Build.fresh
  let b4 ← Build.fresh
  let b5 ← Build.fresh
  let e ← Build.fresh
  let z ← Build.fresh
  let r1 ← Build.fresh
  let r2 ← Build.fresh
  let w ← Build.fresh
  pure (.eq (polePolyOf B ![b0, b1, b2, b3, b4, b5] e z r1 r2 w) 0)

/-- **The pole template** (template index `5`). -/
noncomputable def poleTemplate : ExPoly := Build.template 1 (poleBuild (X 0))

/-- The pole polynomial in the variables of the template: `B = X₀`, `bᵢ = X_{1+i}`, `e = X₇`,
`z = X₈`, `r₁ = X₉`, `r₂ = X₁₀`, `w = X₁₁`. -/
noncomputable def polePolyX : Poly :=
  polePolyOf (X 0) ![X 1, X 2, X 3, X 4, X 5, X 6] (X 7) (X 8) (X 9) (X 10) (X 11)

theorem poleBuild_run : poleBuild (X 0) ⟨1, []⟩ = (.eq polePolyX 0, ⟨12, []⟩) := rfl

theorem poleTemplate_params : poleTemplate.params = 1 := rfl

theorem poleTemplate_witnesses : poleTemplate.witnesses = 11 := rfl

theorem poleTemplate_wf : poleTemplate.WF := by
  refine Build.template_wf_of_fok 1 _ (G := Avail 12 []) (fun i h => h.1) (by decide)
    (by decide) ?_
  show Build.WP (poleBuild (X 0)) ⟨1, []⟩ fun φ _ => FOk (Avail 12 []) 12 φ
  wp_run (Avail 12 []) 12
  exact FOk.eq (VarsIn.polePoly (VarsIn.X (by decide)) (by scope) (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption)) (VarsIn.zero _)

/-- The polynomial of `pole` is `(B S - 0)² = Q_pole²`. -/
theorem poleTemplate_poly : poleTemplate.poly = (polePolyX - 0) ^ 2 := by
  rw [poleTemplate, Build.template_poly, Build.fullFormula, poleBuild_run, compile_globals_nil,
    Formula.compile_eq]

/-- The value of the pole polynomial of the template at an assignment `x` is
`Q_pole(x₀; x₁, …, x₁₁)`. -/
theorem ev_polePolyX (x : ℕ → ℚ) :
    ev x polePolyX = polePoly (x 0) (fun i => x (i + 1)) (x 7) (x 8) (x 9) (x 10) (x 11) := by
  simp only [polePolyX, polePolyOf, poleBS, poleM, poleH, poleT1, poleT2, polePoly, map_mul,
    map_add, map_sub, map_pow, map_one, map_ofNat, ev_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.sum_univ_six, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  rfl

/-- **Semantics of the pole template.** `Rel_pole(B) ⟺ Φ(B)`: the eleven witnesses of the
template are the eleven witnesses of the pole polynomial, in the same order. -/
theorem poleTemplate_rel_iff (a : Fin 1 → ℚ) : poleTemplate.Rel a ↔ PoleSoluble (a 0) := by
  unfold poleTemplate
  rw [Build.template_rel_iff 1 _ (by rw [poleBuild_run]; simp)]
  simp only [poleBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and,
    Formula.holds_eq, map_zero, ev_polePolyX]
  have h0 : ∀ y : Fin 11 → ℚ, assign 1 11 a y 0 = a 0 := fun y => assign_of_lt a y (by omega)
  constructor
  · rintro ⟨y, hy⟩
    rw [h0] at hy
    exact ⟨_, _, _, _, _, _, hy⟩
  · rintro ⟨b, e, z, r1, r2, w, h⟩
    refine ⟨![b 0, b 1, b 2, b 3, b 4, b 5, e, z, r1, r2, w], ?_⟩
    rw [h0]
    convert h using 2
    · funext i
      fin_cases i <;> rfl
    all_goals rfl

end ZInQ.Syntax
