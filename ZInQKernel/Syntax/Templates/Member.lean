import ZInQKernel.Syntax.Templates.Scope

/-!
# The membership and raw addition templates

Templates `0` (`member`, 5 parameters, 7 witnesses) and `1` (`raw_add`, 15 parameters,
6 witnesses) of the library: `EllipticCore.member` and `EllipticCore.addRelation` of
`construction/rational-elliptic-core.js`, defined through `addCore` in
`construction/multiplication-certificate.js`. Neither has rational constants, so the polynomial
is `κ(φ)²`.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-! ### `member` -/

/-- The formula `φ_member` with point `p`, pairs `X`, `Y`, `H` and inverse witness `X_u`:
`⋁(isO(p), ⋀(fin(p), curve(X,Y), N(Y) u ≐ 1, (2Y)·H ≐ 3X² + A, x(p) ≐ x_P, y(p) ≐ y_P))` with
`x_P = H² - 2X` and `y_P = H·(X - x_P) - Y`. -/
noncomputable def memberFormula (p : Code) (X Y H : Pair) (u : ℕ) : Formula :=
  let xP := H.sq.sub (Pair.smul 2 X)
  let yP := (H.mul (X.sub xP)).sub Y
  .or [isO p, .and [fin p, curve X Y, nzFormula Y.norm u,
    feq ((Pair.smul 2 Y).mul H) ((Pair.smul 3 X.sq).add Pair.A), feq p.x xP, feq p.y yP]]

/-- The construction of `member` on the point `p`: the pairs `X`, `Y`, `H`, then the inverse
witness of `NZ_K(Y)`. -/
noncomputable def memberBuild (p : Code) : Build Formula := do
  let X ← Build.freshPair
  let Y ← Build.freshPair
  let H ← Build.freshPair
  let u ← Build.freshIdx
  pure (memberFormula p X Y H u)

/-- **The membership template** (template index `0`). -/
noncomputable def memberTemplate : ExPoly := Build.template 5 (memberBuild (varPoint 0))

theorem memberBuild_run :
    memberBuild (varPoint 0) ⟨5, []⟩ =
      (memberFormula (varPoint 0) (varPair 5) (varPair 7) (varPair 9) 11, ⟨12, []⟩) := rfl

theorem memberTemplate_params : memberTemplate.params = 5 := rfl

theorem memberTemplate_witnesses : memberTemplate.witnesses = 7 := rfl

theorem memberTemplate_wf : memberTemplate.WF := by
  refine Build.template_wf_of_fok 5 _ (G := Avail 12 []) (fun i h => h.1) (by decide)
    (by decide) ?_
  show Build.WP (memberBuild (varPoint 0)) ⟨5, []⟩ fun φ _ => FOk (Avail 12 []) 12 φ
  wp_run (Avail 12 []) 12
  scope

/-- The polynomial of `member` is `κ(φ_member)²` with the variables of the article. -/
theorem memberTemplate_poly :
    memberTemplate.poly =
      (memberFormula (varPoint 0) (varPair 5) (varPair 7) (varPair 9) 11).compile ^ 2 := by
  rw [memberTemplate, Build.template_poly, Build.fullFormula, memberBuild_run]
  exact compile_globals_nil _

/-- The relation of `member`: some witnesses satisfy `φ_member`. -/
theorem memberTemplate_rel_iff (a : Fin 5 → ℚ) :
    memberTemplate.Rel a ↔ ∃ y : Fin 7 → ℚ,
      (memberFormula (varPoint 0) (varPair 5) (varPair 7) (varPair 9) 11).Holds
        (assign 5 7 a y) := by
  unfold memberTemplate
  rw [Build.template_rel_iff 5 _ (by rw [memberBuild_run]; simp)]
  simp only [memberBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and]

/-! ### `raw_add` -/

/-- The output conjunction `out(m)` of a branch with slope `m`:
`⋀(fin(r), x(r) ≐ x_r, y(r) ≐ m·(x - x_r) - y)` with `x_r = m² - x - x'`. -/
noncomputable def addOut (r : Code) (x y x' m : Pair) : Formula :=
  let xr := (m.sq.sub x).sub x'
  .and [fin r, feq r.x xr, feq r.y ((m.mul (x.sub xr)).sub y)]

/-- The formula `φ_add = ⋁(β₁, …, β₅)` of raw addition `r = p + q`, with slope pairs `m_g`,
`m_d` and inverse witnesses `X_{u_g}`, `X_{u_d}`. -/
noncomputable def rawAddFormula (p q r : Code) (mg md : Pair) (ug ud : ℕ) : Formula :=
  let both : Formula := .and [fin p, fin q]
  .or [.and [isO p, peq q r],
    .and [fin p, isO q, peq p r],
    .and [both, feq p.x q.x, feq p.y q.y.neg, isO r],
    .and [both, nzFormula (q.x.sub p.x).norm ug, feq ((q.x.sub p.x).mul mg) (q.y.sub p.y),
      addOut r p.x p.y q.x mg],
    .and [both, feq p.x q.x, feq p.y q.y, nzFormula p.y.norm ud,
      feq ((Pair.smul 2 p.y).mul md) ((Pair.smul 3 p.x.sq).add Pair.A), addOut r p.x p.y q.x md]]

/-- The construction of `raw_add` on the points `p`, `q`, `r`: the slope pairs `m_g`, `m_d`,
then the inverse witnesses of the general and the doubling branch. -/
noncomputable def rawAddBuild (p q r : Code) : Build Formula := do
  let mg ← Build.freshPair
  let md ← Build.freshPair
  let ug ← Build.freshIdx
  let ud ← Build.freshIdx
  pure (rawAddFormula p q r mg md ug ud)

/-- **The raw addition template** (template index `1`). -/
noncomputable def rawAddTemplate : ExPoly :=
  Build.template 15 (rawAddBuild (varPoint 0) (varPoint 5) (varPoint 10))

theorem rawAddBuild_run :
    rawAddBuild (varPoint 0) (varPoint 5) (varPoint 10) ⟨15, []⟩ =
      (rawAddFormula (varPoint 0) (varPoint 5) (varPoint 10) (varPair 15) (varPair 17) 19 20,
        ⟨21, []⟩) := rfl

theorem rawAddTemplate_params : rawAddTemplate.params = 15 := rfl

theorem rawAddTemplate_witnesses : rawAddTemplate.witnesses = 6 := rfl

theorem rawAddTemplate_wf : rawAddTemplate.WF := by
  refine Build.template_wf_of_fok 15 _ (G := Avail 21 []) (fun i h => h.1) (by decide)
    (by decide) ?_
  show Build.WP (rawAddBuild (varPoint 0) (varPoint 5) (varPoint 10)) ⟨15, []⟩
    fun φ _ => FOk (Avail 21 []) 21 φ
  wp_run (Avail 21 []) 21
  scope

/-- The polynomial of `raw_add` is `κ(φ_add)²` with the variables of the article. -/
theorem rawAddTemplate_poly :
    rawAddTemplate.poly = (rawAddFormula (varPoint 0) (varPoint 5) (varPoint 10) (varPair 15)
      (varPair 17) 19 20).compile ^ 2 := by
  rw [rawAddTemplate, Build.template_poly, Build.fullFormula, rawAddBuild_run]
  exact compile_globals_nil _

/-- The relation of `raw_add`: some witnesses satisfy `φ_add`. -/
theorem rawAddTemplate_rel_iff (a : Fin 15 → ℚ) :
    rawAddTemplate.Rel a ↔ ∃ y : Fin 6 → ℚ,
      (rawAddFormula (varPoint 0) (varPoint 5) (varPoint 10) (varPair 15) (varPair 17) 19
        20).Holds (assign 15 6 a y) := by
  unfold rawAddTemplate
  rw [Build.template_rel_iff 15 _ (by rw [rawAddBuild_run]; simp)]
  simp only [rawAddBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and]

end ZInQ.Syntax
