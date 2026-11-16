# pel-hodge results log

Base: 60a3fac7 (leaf-fold28b) + merges of origin/wip/unif-topology (dbf043a4, includes unif-printed 9c2e1809) and
origin/wip/holfam (93220b34); both merged cleanly.

Build tree: copied (reflink) from ~/dzq-wt/holfam (.lake/build, lean/.lake/build; fold25 sources) plus
UniformizationPrinted.olean from ~/dzq-wt/unif-printed. The early chain modules used (TailC, TailQ, HDecomp/*) have
identical sources in fold25 and fold28b; TailX..TailZ36 differ (igusaGL2 removed), so modules importing TailZ40
(HolFamilyPrinted) are checked against the fold25 build of their (unchanged) imports.

## Compile outcomes
- T1.lean (definitions H1, loopClass, IsHodgeFibre): compiles (VERIFIED, 2026-11-16 00:10).
- T2.lean: `isUniformization_of_H1` (H1 form -> lattice form, from UniformizationLeafAll) and
  `exists_H1_of_isUniformization` (converse) compile, no sorry (VERIFIED, 2026-11-16 ~01:00).
  Mathlib API used: IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite(_injective, _apply_mk_eq),
  Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup, ZLattice.rank, IsZLattice.span_top,
  finrank_real_of_complex, LinearMap.injective_iff_surjective_of_finrank_eq_finrank.
- Pitfall: `γ` is a reserved token under these opens (use `lp`).
- ZInQKernel/Contrib/OneProof/PELHodge.lean (imports HolFamilyPrinted, UniformizationPrinted): 0 errors, 0 warnings
  (`lake env lean`, ~8 s on the copied tree). Olean written with `lake env lean -o` (no lake rebuild of the chain).
- scratch/pel-hodge/Discharges.lean (Main + Discharges + PELHodge, fold25 tree): "63 open hypotheses, 2304 theorems
  checked, 9 discharge one" (the 7 pre-existing + 2 of UnifPrinted, imported through PELHodge); no PELHodge theorem
  matches an open field (expected: pelHolFamily is not a field before holfam's fold). All 18 `#print axioms`:
  [propext, Classical.choice, Quot.sound]. Output: Discharges-output.txt.
- scratch/pel-hodge/BypassFold.lean (holfam's dry run, field pelHolFamily -> pelHolFamilyHodge): compiles;
  sixContactMin_of_open31 and frozenTarget_pelHodge standard axioms. Output BypassFold-output.txt.
- scratch/pel-hodge/BypassFoldPi0.lean (same, the three consumers via gonzalezRotgerX6Ab instead of
  deligneComponentsX6PrintedAb): compiles; frozenTarget_pelHodgePi0 standard axioms. Remaining reader of
  deligneComponentsX6PrintedAb there: x6Rows_of18 only (pi0-prune's reroute).
- Specs: autofold.json (after holfam's fold: discharge pelHolFamily by pelHolFamily_of_hodge, leaf
  pelHolFamilyHodge), autofold-bypass.json (holfam's bypass with pelHolFamilyHodge; consumers and consumers_pi0).
  Neither can be dry-run by autofold.py on this base (pelHolFamily is not a field; the bypass is a hand fold).

## Statements (VERIFIED by compile)
- H1 A := Abelianization (FundamentalGroup (A.Pt ℂ) 1), topology UnifPrinted.classicalTopology.
- H1Form A Λ e := IsAnalyticHom id e ∧ (∀ v ∈ Λ, e v = 1) ∧ ∃ lp : Λ → Path 1 1,
  (∀ v t, lp v t = e ((t:ℂ) • v)) ∧ Bijective (v ↦ loopClass (lp v)).
- IsHodgeFibre τ P := ∃ e, H1Form P.A (qmLattice τ) e ∧ IotaCompatible P e.
- PELHolFamilyHodge := holfam's PELHolFamily with IsHodgeFibre τ P as the fibre clause.
- h1Form_iff (hU : UniformizationLeafAll) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
  H1Form A Λ e ↔ IsUniformization id Λ e.  pelHolFamilyHodge_iff hU : PELHolFamilyHodge ↔ PELHolFamily.
- gagaMorphism not used.
