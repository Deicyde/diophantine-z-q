# Blueprint audit of the size and model chapters (task bp-audit-size)

Scope: the 87 articles under `blueprint/roadmap/size/` (36) and `blueprint/roadmap/model/` (51)
whose frontmatter has `statement: formalized`, at commit `de90139`. For each article the
statement (the text before **Proof sketch.**) was compared with the Lean declarations named in
its `lean:` field.

- All 36 size articles are new since the previous Lean statement audit
  (`lean-audit-2026-11-06.md`, commit `0bea4dc`), so all of them were audited.
- In `model/`, the 8 articles formalized since then were audited. Two more were re-checked
  because their text or `lean:` list changed: `descent/torsion.md` and
  `field/division-polynomial-multiples.md`.
- The other 41 model articles were covered by the previous audit. Neither their text nor their
  Lean changed since `0bea4dc`. The Lean changes in `Model/` were limited to these:
  - `toK0_ne_zero` and `toK0_star` moved into `Model/Field/Basic.lean`;
  - a duplicate alias of `mulByN_formulas` was removed;
  - one docstring changed.

## Summary

- **No Lean statement is weaker than its article on the mathematics.** Four articles in
  `size/majorants/` differed from the Lean, and their prose was edited (see "Edits"):
  - `admissible-cutoff.md` claimed a bound on constant nodes that the Lean does not state, and
    it omitted the constructor bounds and the program-literal hypothesis.
  - `template-heights.md` claimed "every other constant is below $2^{128}$", which nothing proves.
  - `recipe-heights.md` omitted the constructor bounds and the circuit-shape hypothesis.
  - `node-majorant.md` left the constructor-bounds hypothesis implicit.
- **Extra Lean hypotheses**, all expected and discharged elsewhere:
  - `HaltingNodeCheck` in `Pstar_size`, `Pstar_target_bounds`, `Pstar_degree_coeff` and
    `PstarNat_maj` (syntax-bounds, degree-coefficient-bound). It is the named finite check,
    as expected.
  - `PrecisionShape N c₃` in `recipe_heights`. It follows from `HaltingNodeCheck`
    (`precisionShape_of`). It is now stated in the article.
  - `|c₃| < 2^(2^24)` for the program literal in `admissible_cutoff`, `PstarNat_maj`,
    `Pstar_degree_coeff`, `Pstar_size` and `Pstar_target_bounds`. The Lean statements quantify
    over every literal `c₃` with this bound. For the actual literal the bound is
    `c3_natAbs_lt` (Assembly/Top/Assembly.lean), which the final audit also recorded. It is now
    stated in admissible-cutoff. In syntax-bounds and degree-coefficient-bound, $P_*$ is the
    specified polynomial at the actual literal, so the hypothesis is discharged there; their
    prose was left unchanged.
  - `ConstructorBounds I B` in `nodes_majorant`, `library_majorant` and `LibraryAdmissible`.
    The constructors are an abstract record. `specConstructors_bounds` proves the bounds for
    the constructors of the specification at every `B ≥ 2^20`. It is now stated in the
    articles.
- **Names.** Every name in the audited `lean:` fields exists. `#print axioms` gives only
  `propext`, `Classical.choice` and `Quot.sound`, or a subset of them: no `sorryAx` in any size
  or model declaration listed. Some lists are incomplete, though the claims are proved; see
  the last section.
- `lake build ZInQKernel` succeeds (only Main.lean's expected `sorry`).
  `uv run --project ~/autoform-dzq autoform check blueprint --lean-root .` passes after the
  edits (353 articles, 897 names resolved).

## Verdicts: size/

Names are in `ZInQ.Size` unless marked otherwise.

| Article | Lean names | Verdict | Changes |
| --- | --- | --- | --- |
| size/constants/small-constant-bounds.md | small_constant_bounds | faithful | none |
| size/constants/closed-comparisons.md | closed_comparisons | faithful (item by item, same numerals) | none |
| size/constants/catalogue-bounds.md | catalogue_bounds | faithful. Lean indexes catalogue primes from 0, so `j < 22` is the article's $1\le j\le22$ | none |
| size/constants/catalogue-size.md | catalogue_size | faithful | none |
| size/constants/formal-multiple-size.md | formal_multiple_size | faithful. Lean is slightly stronger: $1\le M_0\le N_s^{10}$ needs only $N_s\ge1$, unconditional by `Syntax.Ns_pos` | none |
| size/constants/d-bounds.md | D_bounds | faithful | none |
| size/constants/r-equals-d.md | r_equals_d, R_eq_D | faithful | none |
| size/constants/t-identity.md | t_identity | faithful. $T=(48A_{\rm ht})^{13}$ is the definition `Syntax.T_eq` | none |
| size/constants/t-bound.md | closedT_lt | faithful | none |
| size/cutoff.md | literal_cutoff, formal_multiple_succeeds | faithful. The formal-multiple part is unconditional, as the article says | none |
| size/syntax-bounds.md | Pstar_size, Pstar_target_bounds | faithful, with extra hypotheses `HaltingNodeCheck` (expected) and $\lvert c_3\rvert<2^{2^{24}}$ (discharged by `c3_natAbs_lt`). The variable count is the type `Fin 292890231905` | none |
| size/formal-multiple/reduction-homomorphism.md | E0sub, E1sub, redK, reductionHom, ker_reductionHom, E0_eq_top_of_good, zsmul_addOrderOf_mem_E1 | faithful, Lean stronger: any field $k$ with $\rho:\mathbb Z[s]\to k$ of kernel $(\pi)$, and $A\in K_0$ integral at $\pi$ | none |
| size/formal-multiple/trivial-point-count.md | card_affineSolutions_le, card_points_le, addOrderOf_le_two_card_add_one, odd_prime_count_bounds | faithful, Lean stronger (any characteristic) | none |
| size/formal-multiple/reduction-orders.md | exists_reduction_multiple | faithful | none |
| size/formal-multiple/bad-place-congruences.md | bad_place_congruences, bad_place_congruences_zmod | faithful | none |
| size/formal-multiple/bad-place-reduction.md | genP0_mem_E0_d, redK_genP0_d, resK_genA_d, E0_eq_top_of_ne_d | faithful | none |
| size/formal-multiple/odd-coefficient-extraction.md | padicValRat_coords_ge | faithful. "$u_i\ne0\to$" with `padicValRat` encodes $v_p(0)=+\infty$ | none |
| size/formal-multiple/formal-multiple-existence.md | exists_formal_multiple, leastFormalMultiple_bounds, leastFormalMultiple_formalCondition, M0_bounds | faithful | none |
| size/majorants/syntax-height.md | Maj, nodeHeight, nodeHeights, templateHeight, libraryHeights, recipeHeight, recipeHeights | faithful (missing references have height 0, as documented) | none |
| size/majorants/majorant-rules.md | Maj.mono, Maj.X, Maj.C, Maj.add, Maj.mul, Maj.bind₁, Maj.constructor, Maj.rename, Maj.bind₁_of_maj_zero, Maj.sum_sq, Maj.prod | faithful, Lean stronger: rules 5 and 6 allow $m=0$ | none |
| size/majorants/node-majorant.md | ConstructorBounds, NodeAdmissible, nodes_majorant, library_majorant | the Lean hypothesis `ConstructorBounds I B` was implicit in the article | stated the uniform-bounds hypothesis on the constructors, and that the constructors of the specification satisfy it at every $B\ge2^{20}$ (`specConstructors_bounds`); proof sketch adjusted |
| size/majorants/recipe-majorant.md | model_majorant, composition_majorant | faithful, Lean stronger: no $h_\kappa\ge1$, and $m=0$ calls allowed | none |
| size/majorants/template-heights.md | templateHeightTable, LibraryAdmissible, templateLibrary_maj | **drift**: "every other constant of the library is below $2^{128}$" and "compared with $2^{128}$ by evaluation" are not Lean facts. The tactic bounds each literal by $2^{2^k}$ and needs no hypothesis | replaced both sentences by what the Lean does |
| size/majorants/recipe-heights.md | recipe_heights | **drift**: the hypotheses were "the four node hypotheses". Lean needs `LibraryAdmissible` (constructor bounds, psi indices, $\ell$, $T$; no constant hypothesis) and `PrecisionShape N c₃` | restated the hypotheses (template-height hypotheses and the circuit shape as upper bounds); "has at most 293622 constraints" |
| size/majorants/admissible-cutoff.md | admissible_cutoff, D_le_T | **drift**. Item 1 ($\lvert c\rvert\le T$ for constant nodes) is not proved: `LibraryAdmissible` has no constant field, and only $2^{69}<T$ exists. The constructor bounds (a field of `LibraryAdmissible`) were missing, and so was the hypothesis $\lvert c_3\rvert<2^{2^{24}}$ | restated as the template-height hypotheses with the constructors of the specification; added the $c_3$ hypothesis and $D\le T$; rewrote the proof sketch (removing a tooling remark) |
| size/majorants/degree-coefficient-bound.md | Pstar_degree_coeff, PstarNat_maj | faithful, with extra hypotheses `HaltingNodeCheck` (expected) and $\lvert c_3\rvert<2^{2^{24}}$ (discharged) | none |
| size/majorants/tower-comparison.md | tower_bounds, degree_lt_tower_seven, coefficient_lt_tower_eight | faithful | none |
| size/norms/l1-norm.md | Syntax.l1, PairRing, pairNorm, pairDeg | faithful | none |
| size/norms/l1-norm-estimates.md | l1_estimates | faithful, Lean stronger (degree bounds for finite sums and products too) | none |
| size/norms/substitution-bounds.md | substitution_bounds, rename_bounds, l1_rename_eq | faithful | none |
| size/norms/pair-norm.md | pair_norm_estimates | faithful | none |
| size/norms/division-polynomial-size.md | normDiv_size, psiComponent_size | faithful (`componentA = -11243 + 7950 s`) | none |
| size/norms/quadratic-heights.md | QRep, QRep.exists_add, exists_sub, exists_mul, exists_two_mul, exists_div, coord_bounds | faithful | none |
| size/norms/coordinate-heights.md | iota_coord_height | faithful ($T\in\mathbb N$) | none |
| size/norms/guard-size.md | guardPoly_size | faithful | none |
| size/norms/constructor-bounds.md | psi_uniform, guard_uniform, const_uniform | faithful | none |

## Verdicts: model/ (new or changed since the previous audit)

Names are in `ZInQ`.

| Article | Lean names | Verdict | Changes |
| --- | --- | --- | --- |
| model/generator.md | generator_certificate, carrierD_eq_zmultiples, indexEquivCarrier, iota_injective | faithful, with no hypothesis. "$D$ is torsion-free" follows from `indexEquivCarrier : ℤ ≃+ carrierD` | none |
| model/membership.md | rel_member_iff | faithful. The explicit branch description is `MemberSpec`, `memberTemplate_rel_iff_spec` | none |
| model/membership-indices.md | rel_member_iff_iota, rel_member_iff_existsUnique_iota | faithful | none |
| model/raw-addition-points.md | rel_rawAdd_iff | faithful. The five branches are `RawAddSpec`, where the template writes $y_r=m(x-(m^2-x-x'))-y$, equivalent given $x_r$ | none |
| model/raw-addition.md | rel_rawAdd_iota | faithful | none |
| model/descent/nonzero-multiples.md | genP0_not_isOfFinAddOrder, iota_injective, zsmul_genP0_affine, zsmul_genP0_affine_z_w, iota_zero_coord_iff | faithful, with no hypothesis | none |
| model/descent/torsion.md | mem_torsion_E_iff, card_torsion_E, genP0_not_isOfFinAddOrder, mem_torsion_C_iff, card_torsion_C | faithful. The previous audit's WRONG item ("$P_0$ has infinite order") is resolved by `genP0_not_isOfFinAddOrder` | none |
| model/field/explicit-identities.md | k0_identities, K0.totallyPositive_iff, k0_signs | faithful (item by item) | none |
| model/field/fixed-point-codes.md | iota_eq_psi_unconditional, iota_eq_psi | faithful. The unconditional form needs no hypothesis | none |
| model/field/division-polynomial-multiples.md | mulByN_formulas | faithful (statement unchanged; only the proof sketch changed). The "any field of characteristic zero" sentence is the unlisted `mulByN_formulas_of_charZero` | none |

model/point-codes.md has not changed. Its sentence "distinct indices have distinct codes",
which the previous audit found conditional, is now `iota_injective`, unconditional; it is
recorded in generator.md and nonzero-multiples.md.

## Edits (article prose only; frontmatter, ids and dependency sections untouched)

1. `size/majorants/admissible-cutoff.md`.
   - **Statement.** Items 1–4 now restate the hypotheses of the template heights for
     $B=T+1$:
     - the uniform constructor bounds at $B$ for the constructors of the specification;
     - $1\le\ell\le T$;
     - the division-polynomial indices satisfy $\lvert n\rvert+1\le T+1$;
     - $0\le T\le B-1$.
   - **Hypothesis on $c_3$.** "Let the program literal satisfy $\lvert c_3\rvert<2^{2^{24}}$"
     is now part of the statement.
   - **Added.** $D\le T$ and "the literal constants of the templates need no hypothesis".
   - **Proof sketch.** It uses $D\le R\le Q\le Q^{17}\le A_{\rm ht}\le T$ and
     $\lvert n\rvert+1\le2^{2^{2060}}$, as in the Lean. $2^{69}<T$ is kept only as the
     comparison with the manuscript's checked fact.
2. `size/majorants/template-heights.md`.
   - **Statement.** "every other constant … below $2^{128}$" became "an explicit integer
     literal and needs no hypothesis".
   - **Proof sketch.** The literals are bounded as $\lvert c\rvert\le2^{2^k}$ for small
     explicit $k$, which $B\ge2^{20}$ absorbs.
3. `size/majorants/recipe-heights.md`.
   - **Statement.** The hypotheses are those of the template heights, plus the shape of the
     natural precision circuit as upper bounds:
     - five inputs;
     - at most $54{,}056$ explicit variables, at least five of them inputs;
     - at most $125{,}327$ additions, $98{,}382$ multiplications and $15{,}845$ calls;
     - constants among $0,\pm1,c_3,2,4,1399$.
   - **Proof sketch.** "has at most 293622 constraints".
4. `size/majorants/node-majorant.md`. The uniform-bounds hypothesis on the constructors is now
   stated, with the remark that the constructors of the specification satisfy it at every
   $B\ge2^{20}$. The proof sketch refers to it.

## What must change elsewhere (not done: frontmatter and README are outside this task)

- **Incomplete `lean:` lists** (claims proved under unlisted names):
  - admissible-cutoff: `one_le_ell_value` ($\ell\ge1$), `specConstructors_bounds`,
    `two_pow_sixtynine_lt_T`.
  - node-majorant: `library_nodes_majorant` (the claim for every node of every template),
    `specConstructors_bounds`.
  - template-heights: `psiIndices` (where the division-polynomial constructors occur),
    `templateLibrary_maj_lean`.
  - recipe-heights: `powerValueRecipe_conjuncts_length`,
    `precisionRecipe_conjuncts_length_le`; the shape is `Syntax.PrecisionShape` and
    `precisionShape_of`.
  - bad-place-reduction: `resK_genP0_d`, `vge_genX0_d`, `nonsingular_two_six`.
  - trivial-point-count: `addOrderOf_le_two_natCard_add_one`.
  - generator: `zsmul_genP0_injective`, `mem_carrierD_iff_exists_zsmul`.
  - membership: `MemberSpec`, `memberTemplate_rel_iff_spec`, `rel_member_iff_isCarrierCode`.
  - raw-addition-points: `RawAddSpec`, `rawAddTemplate_rel_iff_spec`.
  - fixed-point-codes: `psiP0`, `fixedX`, `fixedY`.
  - division-polynomial-multiples: `mulByN_formulas_of_charZero` (repeated from the previous
    audit).
- **`size/majorants/README.md`.** It still says the majorant needs $B$ to exceed "every
  occurring constant". The Lean needs no bound on the literal constants, but it does need the
  uniform constructor bounds. The README has no `statement:` field and was left as is.
- **No consumer is weakened.**
  - The four edited articles are consumed by recipe-heights, admissible-cutoff and
    degree-coefficient-bound. These are exactly the Lean chain
    `admissible_cutoff → integers_maj → PstarNat_maj → Pstar_degree_coeff`, which compiles.
  - The node-list theorem (`library_majorant`) is not used for the constructed library, whose
    templates are not node lists. template-heights proves the constructed library directly.

## Method

- I read every in-scope article statement against the Lean source of each listed declaration
  and of the definitions it uses:
  - `Syntax/Constants/Fixed.lean`, `FormalMultiple.lean` and `Guard.lean`;
  - `Syntax/Recipes/Precision.lean` and `Literal.lean`;
  - `Model/DivisionPolynomials/*`.
- One scratch file ran `#print axioms` on all 118 names from the audited `lean:` fields. All
  resolved, with no `sorryAx`.
- Lean ran one process at a time, with the load well below the limit.
