# model-top: the top level of the elliptic model chapter

Modules: `ZInQKernel/Model/Generator/` (root `ZInQKernel/Model/Generator.lean`, imported by
`ZInQKernel.lean`). Every declaration below is proved; nothing in these modules uses `sorry`,
`native_decide` or any axiom besides `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms` on the main results). The branch merges `origin/wip/syntax-templates` (for
`memberTemplate`, `rawAddTemplate`); none of its files were edited.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| (no article yet: infinite order of `P₀`) | `ZInQ.genP0_not_isOfFinAddOrder` (`Generator/InfiniteOrder.lean`) | proved |
| `model/generator.md` | `ZInQ.two_smul_range_eq_zmultiples`, `ZInQ.carrierD_eq_zmultiples`, `ZInQ.generator_certificate`, `ZInQ.indexEquivCarrier`, `ZInQ.eq_zero_of_mem_carrierD_of_isOfFinAddOrder`, `ZInQ.iota_injective` (`Generator/Certificate.lean`, `Generator/InfiniteOrder.lean`) | proved |
| `model/membership-indices.md` | `ZInQ.rel_member_iff_iota`, `ZInQ.rel_member_iff_existsUnique_iota` (`Generator/Membership.lean`) | proved |
| `model/membership.md` | `ZInQ.rel_member_iff` (also `ZInQ.rel_member_iff_isCarrierCode`) (`Generator/Membership.lean`) | proved |
| `model/raw-addition-points.md` | `ZInQ.rel_rawAdd_iff` (`Generator/RawAddition.lean`) | proved |
| `model/raw-addition.md` | `ZInQ.rel_rawAdd_iota` (`Generator/RawAddition.lean`) | proved |

Statements as formalized:

- `genP0_not_isOfFinAddOrder : ¬ IsOfFinAddOrder genP0` (from `two_nsmul_eq_zero_of_isOfFinAddOrder`
  and `genCurve_two_torsion`: `P₀` is affine with `y₀ ≠ 0`). Also `addOrderOf_genP0 : addOrderOf genP0 = 0`.
- `two_smul_range_eq_zmultiples : (nsmulAddMonoidHom (α := genCurve.toAffine.Point) 2).range = AddSubgroup.zmultiples genP0`;
  `carrierD_eq_zmultiples : carrierD = AddSubgroup.zmultiples genP0`;
  `generator_certificate : ¬ IsOfFinAddOrder genP0 ∧ carrierD = AddSubgroup.zmultiples genP0`;
  `indexEquivCarrier : ℤ ≃+ carrierD` with `indexEquivCarrier n = n • genP0`;
  `eq_zero_of_mem_carrierD_of_isOfFinAddOrder` (D is torsion-free); `iota_injective : Function.Injective iota`.
- `rel_member_iff (p : Fin 5 → ℚ) : memberTemplate.Rel p ↔ ∃ Q ∈ (nsmulAddMonoidHom (α := genCurve.toAffine.Point) 2).range, p = pointCode Q`.
- `rel_member_iff_iota (p) : memberTemplate.Rel p ↔ ∃ n : ℤ, p = iota n`, and
  `rel_member_iff_existsUnique_iota (p) : memberTemplate.Rel p ↔ ∃! n : ℤ, p = iota n`.
- `rel_rawAdd_iff (P Q : genCurve.toAffine.Point) (r : Fin 5 → ℚ) : rawAddTemplate.Rel (Fin.append (Fin.append (pointCode P) (pointCode Q)) r) ↔ r = pointCode (P + Q)`.
- `rel_rawAdd_iota (a b : ℤ) (R : Fin 5 → ℚ) : rawAddTemplate.Rel (Fin.append (Fin.append (iota a) (iota b)) R) ↔ R = iota (a + b)`.

## Statement corrections and differences

1. **No Mordell–Weil hypothesis.** `generator.md` and `membership-indices.md` say "Assume the
   Mordell-Weil hypothesis". Mordell–Weil is proved (`mordellWeilE`, used through
   `exists_generator_C'`), so the Lean statements take no `hMW` argument. The articles should
   drop the assumption, and their "Depends on: Mordell–Weil for the generator curve" should point to
   the proved theorem (`model/descent/mordell-weil-from-descent.md`) under "Proof depends on".
2. **Relation notation.** The implementation notes write `RelTemplate memberTemplate p`. The syntax
   chapter's relation is `ZInQ.Syntax.ExPoly.Rel`, so the statements say `memberTemplate.Rel p` and
   `rawAddTemplate.Rel a`. The fifteen raw-addition parameters `(p, q, r)` are
   `Fin.append (Fin.append p q) r`, which is `Fin 15 → ℚ` up to definitional unfolding.
3. **`model/membership-indices.md`** says "and the integer n is then unique". This is formalized
   twice: as `∃` (`rel_member_iff_iota`) and as `∃!` (`rel_member_iff_existsUnique_iota`).
4. **Raw-addition branches (4) and (5).** The article writes `y_r = m(x - x_r) - y`. The template uses
   `y_r = m(x - (m² - x - x')) - y`. Given the abscissa equation the two agree. `RawAddSpec` uses
   the template's form so that it matches the formula literally.
5. **Generator proof.** The proof follows the sketch, with one change. "Search box" and "finite search"
   are used together through `small_point_abscissa` (Heights): a point with `h_x < log 9` has its
   abscissa among the seven survivors. Equal abscissas give equal or opposite points through
   Mathlib's `Y_eq_of_X_eq`.

## Lemmas added beyond the leaves

- `Generator/InfiniteOrder.lean`: `two_nsmul_genP0_ne_zero`, `addOrderOf_genP0`, `iota_injective`.
- `Generator/Certificate.lean`:
  - `curveC_eq_or_eq_neg_of_X_eq` (equal abscissas on `C`).
  - `canonHeight_eq_of_X_eq_translate`, `two_nsmul_eq_zero_of_X_two_torsion`.
  - `canonHeight_eq_of_hx_lt`: a nontorsion `S` with `h_x(S) < log 9` has `ĥ(S) = ĥ(R)`.
  - `abs_free_index_eq_one`: if `R = [m]S + T` with `S` nontorsion, then `|m| = 1`.
  - `two_nsmul_range_C_eq_zmultiples` (`2C(K₀) = ℤ[2]R`), `genP0_eq_two_nsmul` (`P₀ = [2]θ⁻¹(R)`).
  - `mem_carrierD_iff_exists_zsmul`, `zsmul_genP0_injective`, `indexEquivCarrier_apply`.
- `Generator/GroupLaw.lean` (the group law on `E` in coordinates, reusable):
  - `genCurve_negY`.
  - `genCurve_add_of_X_ne`: chord, for any `m` with `(x₂ - x₁) m = y₂ - y₁`.
  - `genCurve_two_nsmul_of_Y_ne`: tangent, for any `m` with `2 y m = 3x² - d²`.
  - `genCurve_two_nsmul_of_Y_eq_zero`.
  - Code coordinates `codeX`, `codeY` (`⟨c 1, c 2⟩`, `⟨c 3, c 4⟩ : K0`), `eq_pointCode_some_iff`,
    `ne_pointCode_zero_of_apply_zero`.
- `Generator/Membership.lean`:
  - `Syntax.ev_norm_eq` (`ev x u.norm = N([u])`), `K0.C_two`, `K0.C_three`.
  - `holds_memberFormula` (`φ_member` in `K₀`-terms at any assignment).
  - `MemberSpec` (the article's explicit equations), `memberTemplate_rel_iff_spec`, `memberSpec_iff`.
  - Assignment lemmas `evCode_assign_member`, `val_assign_member_{x,y,X,Y,H}`.
- `Generator/RawAddition.lean`:
  - `Syntax.val_code_x/y`, `Syntax.ev_code_zero`.
  - `RawAddSpec` (the five branches in `K₀`-terms), `holds_rawAddFormula`, `rawAddTemplate_rel_iff_spec`.
  - Assignment lemmas `evCode_assign_rawAdd_{p,q,r}`, `val_assign_rawAdd_{mg,md}`, `assign_rawAdd_{ug,ud}`.
  - `pointCode_zero'`, `pointCode_some_ne_O`, `norm_sub_self_mul_ne_one`, `rawAddSpec_pointCode_iff`.

## Problems

None open. The membership and raw-addition semantics rely on the syntax-templates branch
(`memberTemplate_rel_iff`, `rawAddTemplate_rel_iff`, `holds_*` lemmas of
`Syntax/Language/Pairs.lean`). If that task renames `memberFormula`, `rawAddFormula`, `addOut` or
reorders witnesses, only `holds_memberFormula`, `holds_rawAddFormula` and the assignment lemmas need
updating.

## Suggestions for the next agent

- The blueprint should give `genP0_not_isOfFinAddOrder` its own article (or put it in
  `model/descent/torsion.md`). It needs only the torsion theorem.
- Later chapters (multiplication, natural predicate) should use `rel_member_iff_existsUnique_iota`
  and `rel_rawAdd_iota`. `memberTemplate_rel_iff_spec` and `rawAddTemplate_rel_iff_spec` give
  the explicit equations if a caller needs the witnesses.
- `GroupLaw.lean` has the chord and tangent formulas on `E` in the form the templates use (slope
  given by a linear equation). They may be useful to the multiplication or division-polynomial
  tasks.
