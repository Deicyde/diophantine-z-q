# lkw: local Kronecker–Weber (leaf T16) is proved, and with it leaf T30

**Main result.** These theorems compile with no `sorry`. `#print axioms` shows only `[propext, Classical.choice, Quot.sound]` for each:
- `theorem ZInQ.Contrib.localKroneckerWeber (p : ℕ) [Fact p.Prime] : PkgI6.LocalKroneckerWeber p`
  (ZInQKernel/Contrib/LocalKW/LocalKW.lean). This is leaf T16 / I6.3 exactly, with no extra hypotheses.
- `theorem ZInQ.Contrib.leafSqrtCrit : GlueDescent.B2Q.LeafSqrtCrit` (ZInQKernel/Contrib/LocalKW/T30.lean).
  This is leaf T30 / L-B2c. It feeds the theorem above to t30-adelic's derivation, which is copied unchanged
  except for its namespace into ZInQKernel/Contrib/LocalKW/SqrtCrit.lean.

**Route** (docs/research/lkw.md). Tau Ceti states neither local Kronecker–Weber nor the norm groups of
ℚ_p(μ_m). The proof uses Tau Ceti's local reciprocity and its explicit Artin action on roots of unity
(Local/ArtinMap, Reciprocity, Cyclotomic, ExplicitCyclotomicSymbol/ArtinMap at oct16). It does not use
local existence. The steps:
- (A) `le_of_normGroup_le`: if `N_M ≤ N_L` with `L` abelian, then `L ≤ M`. This follows from the density of the absolute Artin map.
- (C) `normGroup_cyclotomic_le_powerSubgroup`: take `m = p^(2v_p(n)+1)(pⁿ−1)`. Then every norm from ℚ_p(ζ_m) is an n-th power. The argument tracks the unit part and the valuation through the Artin action, and uses Hensel (B).
- (B) `exists_pow_eq_of_norm_sub_one_le`: the Hensel step.
- Since `(ℚ_pˣ)ⁿ ≤ N_L` for `n = [L:ℚ_p]`, `L ≤ ℚ_p(ζ_m)`.

**What compiles.** `lake build ZInQKernel.Contrib.LocalKW.T30` succeeds; this builds LocalKW.Basic, LocalKW.LocalKW, LocalKW.SqrtCrit and LocalKW.T30.
Axiom checks are in scratch/lkw/Axioms.lean and scratch/lkw/AxiomsT30.lean.

**Declarations proved** (namespace `ZInQ.Contrib.LocalKW`, Basic.lean):
- `le_adjoin_rootsOfUnity`, `le_of_normGroup_le`, `fixes_of_mem_normGroup`
- `normGroup_cyclotomic_le_powerSubgroup`, `exists_pow_eq_of_norm_sub_one_le`, `exists_eq_zpow_mul_unit`
- `valuation_unit`, `sepIncl`, `coe_sepIncl`, `artinGal`, `localArtinMap_eq_artinGal`, `artinGal_eq_one_of_mem`
- `norm_natCast_padicInt`, `coprime_self_pow_sub_one`, `zpow_apply_eq_self`

Plus `ZInQ.Contrib.localKroneckerWeber`, `ZInQ.Contrib.leafSqrtCrit`, and the copied
`ZInQ.Contrib.LocalKW.SqrtCrit.*`.

**Dependencies / remaining.**
- The branch merges wip/tc-port, which vendors the Tau Ceti modules, at 395103a4. lkw vendored no Tau Ceti module itself, and wip/kw-new is not needed.
- Nothing in this task's scope remains unproved.
- SqrtCrit.lean must not import Tau Ceti: with Tau Ceti's instances in scope, its `Normal` instance searches time out.
