# tate-module-prints

Two single-print rows on the Tate module `V_p(A) = ℚ_p ⊗ T_p(A)`, and the Lean glue from them to
`DeRhamScholze.HTMerge.VpDualDeRhamAbVar` (vpdual-merge, `VpDualMerge/Row.lean`). tate-prints-fold
(`ZInQKernel/OneProof/H/TailZ106.lean`) made them the added rows of `ZInQ.OneProof.frozenTarget` in
place of `scholzeH1AbVar` and `t10TateDuality`, one print per row, with the glue derived in Lean;
that fold kept the count at 22. Since y3-colmez-1127 (`TailZ113.lean`) the Colmez row is proved
from two rows, `milneThm71Projective` and `colmez1992DeRhamAbVarModel` (`../ColmezProperModel/`),
and `fontaine1982HTAbVar` is still a row.

This directory is add-only and changes no count. It claims no row.

## Files

* `Rows.lean` (namespace `DeRhamScholze.TatePrints`): the two rows, with the prints quoted in
  their docstrings.
  * `Colmez1992DeRhamAbVar` (R1): Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann.
    292 (1992), 629-644, Théorème 5.2 (i)-(ii), p. 639. The period pairing with values in
    `B_dR⁺`, Galois-compatible, non-degenerate over `B_dR` on the `T_p` side, with `H¹_dR(X)`
    weakened to an existential type `H`. Bilinearity in `ω`, the `Fil¹` clause and (iii) are
    dropped (weakenings).
  * `Fontaine1982HTAbVar` (R2): Fontaine, *Formes différentielles et modules de Tate des variétés
    abéliennes sur les corps locaux*, Invent. Math. 65 (1982), 379-409, Théorème 2 (Tate,
    Raynaud), p. 388, in dimension form: `dim_{F'} Hom_{G_F}(V_p(A), ℂ_p(i)) = g` for `i = 1, 0`
    (`htF (A.galRep p) i`). The equality "dimension = g" is printed in the proof on p. 388
    ("chacune de ces dimensions est égale à d"), not in the statement of Théorème 2.
* `Glue.lean`: `vpDual_of_colmezFontaine : Colmez1992DeRhamAbVar → Fontaine1982HTAbVar →
  VpDualDeRhamAbVar`.
  * §1 `Gen` (linear algebra, Mathlib only): a family of `G`-equivariant maps `V → B` (`B` a
    field) that is non-degenerate after base change to `B` spans `Hom_K(V, B)` over `B`
    (`span_eq_top_of_nondeg`, through `LinearMap.liftBaseChangeEquiv` and the dual
    coannihilator); it contains a basis (`exists_basis_of_span`); the coordinates of an
    equivariant map in it are invariant (`repr_fixed`); hence
    `dim_K Hom_G(V, B) = dim_K B^G · dim_K V` (`finrank_of_nondeg`), and the values of every
    equivariant map satisfy any property closed under `0`, `+`, `·` that holds on `B^G` and on the
    values of the family (`forall_prop_of_nondeg`).
  * §2 G1 `dual_deRham_fil0_of_colmez`: from R1, `V_p(A)^∨` is de Rham and
    `Hom_{G_F}(V_p(A), B_dR) ⊆ Hom(V_p(A), B_dR⁺)` (`Fil⁰ D_dR = D_dR`). Uses
    `BdRInv.bdRInvariantsPrinted_proof` (`dim B_dR^{G_F} = [F:ℚ_p]`) and `BdRInv.key` (nonzero
    invariants are units of `B_dR⁺`).
  * §3 G2 `htSpaceOver_eq_bot_of_card`: if the Hodge-Tate dimensions in weights 0 and 1 add up to
    `dim V`, every other Hodge-Tate space vanishes (Tate-Sen `linIndep_two`, Tate's
    `twist_fixed_eq_zero`).
  * §4 G3 `ddr_inf_filH_two_eq_bot`: `D_dR ∩ Fil² = 0` from the vanishing of the weights `j ≥ 2`,
    through `gr^j` (`grJ`, `grJ_mem`, `mem_filH_succ_of_grJ`, generalizing the tree's `gr1`) and
    Krull's intersection theorem in the discrete valuation ring `B_dR⁺`
    (`eq_zero_of_forall_mem_filB`).
  * §5 G4 `vpDual_clauses_of_colmezFontaine`: assembly. The weight-1 equality
    `dim Fil¹ D_dR = [F:ℚ_p] g` comes from `HTAbVar.finrank_fil1_bounds`; the general equality of
    graded pieces with Hodge-Tate multiplicities is not used.
* `FoldCheck.lean`: the bundle `TatePrints.OpenAddedLeaves30` (two fields), its constructor
  `openAddedLeaves30_mk`, the projection `openAddedLeaves29VP_of_tatePrints` to vpdual-merge's
  `OpenAddedLeaves29VP`, `frozenTarget_with_tatePrints` (`frozenTarget`'s body, with the added
  bundle replaced by the two rows, fed through `vpDual_of_colmezFontaine` into
  `OpenAddedLeaves29VP` and `HDec.HSyn.sixContactMin_of_open98_vp`), the same over the bundle
  (`frozenTarget_with_addedLeaves30`), and `#print axioms` for every new theorem.

## Fold plan (not part of this PR)

The fold landed as tate-prints-fold (`ZInQKernel/OneProof/H/TailZ106.lean`, top
`sixContactMin_of_open99`, 22 → 22), before the `y3FullThreeRepZ30` fold (`TailZ109`). Generation
numbers below are for main before this fold (top `sixContactMin_of_open98`, 22 statements).
Draft #212 (the `y3FullThreeRepZ30` fold, 22 → 29) takes the same next generation
(`ZInQKernel/OneProof/H/TailZ106.lean`, `OpenResearchLeaves79`, `sixContactMin_of_open99`).
Whichever fold lands second regenerates on the new main:

* #212 first: this fold becomes `TailZ107.lean` with
  `sixContactMin_of_open100 (r : OpenResearchLeaves79) (t : OpenTextbookLeaves18)
  (l : OpenAddedLeaves30) := sixContactMin_of_open98_vp
  (openResearchLeaves78_of_OpenResearchLeaves79 r) t (openAddedLeaves29VP_of_OpenAddedLeaves30 l)`,
  `ZInQKernel/OneProof/Main.lean` keeps `r : OpenResearchLeaves79`, the count is 29 → 29, and
  `FoldCheck.lean`'s two `frozenTarget_with_*` are restated over
  `OpenResearchLeaves79`.
* this fold first: #212 regenerates as `TailZ107.lean` / `sixContactMin_of_open100` over
  `OpenAddedLeaves30`, its count still 22 → 29.

1. `ZInQKernel/OneProof/H/TailZ106.lean` (`TailZ107` / `sixContactMin_of_open100` if #212 lands
   first):
   ```lean
   structure OpenAddedLeaves30 : Prop where
     colmez1992DeRhamAbVar : DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar
     fontaine1982HTAbVar : DeRhamScholze.TatePrints.Fontaine1982HTAbVar

   theorem openAddedLeaves29VP_of_OpenAddedLeaves30 (n : OpenAddedLeaves30) :
       OpenAddedLeaves29VP where
     vpDual := DeRhamScholze.TatePrints.vpDual_of_colmezFontaine n.colmez1992DeRhamAbVar
       n.fontaine1982HTAbVar

   theorem sixContactMin_of_open99 (r : OpenResearchLeaves78) (t : OpenTextbookLeaves18)
       (l : OpenAddedLeaves30) : ZInQ.SixContactMin :=
     sixContactMin_of_open98_vp r t (openAddedLeaves29VP_of_OpenAddedLeaves30 l)
   ```
   (`FoldCheck.lean` checks the same terms over `TatePrints.OpenAddedLeaves30`.)
2. `ZInQKernel/OneProof/Main.lean`: `frozenTarget (l : HDec.HSyn.OpenAddedLeaves30)` through
   `sixContactMin_of_open99`; the body is `FoldCheck.frozenTarget_with_addedLeaves30`.
   `VpDualDeRhamAbVar` is derived glue, not a row.
3. `docs/one-proof/kinds.tsv`: remove `added scholzeH1AbVar` and `added t10TateDuality`; add two
   rows `added colmez1992DeRhamAbVar` and `added fontaine1982HTAbVar`, kind `published`, strict
   and strictest `GLUE` until each is read (three-lens reading against the original print), with
   the sources and locators above and the reading risks below.
4. `reviews.tsv`: move any rows of the two old fields to `reviews-retired.tsv`. Regenerate
   `OPEN.md` (`scripts/one_proof/render_open.py`); also regenerate
   `docs/one-proof/open-statements.json` and the `Main.lean` narrative paragraph, as the fold
   tooling does.
5. Count: 17 research + 2 added + 3 `frozenTarget` hypotheses = 22: 22 → 22 on main before the fold;
   29 → 29 if #212 lands first.
   The GLUE tally is unchanged at the fold; if both readings pass, both rows become LEAF
   (published single prints). `ScholzeH1AbVar`, `T10_TateDuality` and the `HTMerge` theorems stay
   in the tree for the superseded tops.

## Reading risks

1. **R1, points.** Colmez builds `T_p(X)` from `u_n ∈ 𝒳(O_{C_p}) = X(C_p)` (p. 639); the row's
   `V_p(A)` is built from the `F̄`-points of `A`. A reading needs the identification
   `A[pⁿ](F̄) ≅ A[pⁿ](ℂ_p)`, `G_F`-equivariantly (torsion points are algebraic over `F̄`). This
   PR does not prove it in Lean; `../ColmezTorsionIso/` does (`torsion_iso`,
   `vCp_galRep`), and since y3-colmez-1127 the Lean chain uses it to derive R1 from
   `milneThm71Projective` and `colmez1992DeRhamAbVarModel`.
2. **R1, weakenings.** `H¹_dR(X)` becomes an existential type; bilinearity in `ω`, the `Fil¹`
   clause and (iii) are dropped. The kept non-degeneracy is the `T_p` side of "non-dégénérée
   quand on étend les scalaires à B_dR". The row is not vacuous: for `g > 0` an empty `H` makes
   the non-degeneracy clause false.
3. **R2, count in the proof.** "= g" is printed on p. 388 in the deduction of Théorème 2 from
   Théorème 2', not in Théorème 2's statement. A reader who rates it CONSEQUENCE would name the
   missing step `dim_K H⁰(X, Ω¹) = dim_K H¹(X, O_X) = d`.
4. **Period ring.** Mathlib's `BDeRhamPlus` and `BdR = Frac(B_dR⁺)` against Fontaine's `B_dR`
   (Colmez §2, p. 632); the same identification as in the existing `B_dR` rows
   (`TDict.bdREquivAwayT`).
5. **Twists and fields.** `C(1) = C ⊗ lim μ_{pⁿ}` is `htF ρ 1` (σ acting by `χ(σ)σ`); Fontaine's
   `K` is the image `F' ⊆ ℚ̄_p` of `F`; `Hom_{Z_p[G]}(T_p, C(i)) = Hom_{G_F}(V_p, ℂ_p(i))` since
   `C(i)` is a `ℚ_p`-space.
