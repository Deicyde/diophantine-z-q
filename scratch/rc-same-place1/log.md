# rc-same-place1 results log

Base 8b140cd2a. Setup checks: CharFreeSeamTwo.lean, GoodRowWire/SamePlace.lean, rc-hcm-v21g.md exist; `structure OperatorComparison` present. OK.

## Item 1 (doc fixes)
- docs/research/rc-goodrow-wire.md: point/point_W/point_frob/frobenius_sq rows, SamePlaceData owner text, sp row, X row, point_W type row rewritten (owners per generic7 item 1(n)).
- .fleet/rc-goodrow-wire.md: owner paragraph, sp bullet, X bullet.
- docs/research/rc-hcm-v21g.md: only the JetchevKane.classes row.

## Session 2 (resumed after item 1)
- Dependency build (one lake process): CharFreeSeamTwo, PMAdelic.Comparison, GoodRowWire.SamePlace, ModelTarget.Read, Y0LevelPoints. RC was not built in this worktree; Mathlib/vendored oleans present.
- Files drafted under ZInQKernel/Contrib/OneProof/RC/SamePlace/: Supersingular, PointForm, FrobeniusTwist, AtkinLehner, FrobeniusSquare.
- Design: IsSupersingular takes `ell` explicitly (`IsSupersingular ell E`, `ssPoint K ell N`), not `ringChar K`; same predicate for K of characteristic ell.
- resAlgebra ell K := (ModelTarget.resRing ell K).toAlgebra (abbrev, local instance) is the LocalIntegers ell-structure.
- φ lemma hypothesis on f.left stated as `letI := ModelGeneric5.levelCommRing h₅ htame h₂; f.left = Spec.map (ofHom φ)`.
- 6(d) proved by order arithmetic (Q•P, ell•P, gcd(Q,ell)=1) instead of CRT decomposition; same content.

## Build outcomes (one lake process each; axiom tails in scratch/rc-same-place1/build-*.txt)
- SamePlace.Supersingular: builds (commit 6a1c4b87d). Fix: universe error from an inner ∀ over Type* in torsionBy_eq_bot_congr; split into torsionBy_eq_bot_of_addEquiv.
- SamePlace.PointForm: builds (a39316b0e). Fixes: `apply algHom_ext_spec` unfolded pointForm (Subalgebra.toSemiring vs CommRing.toSemiring on coercions); went through specOf/specOf_injective. Over.pullback_map_left did not rewrite (instance path); used `simp` for the `.left ≫ pullback.fst` step.
- SamePlace.FrobeniusTwist: builds (d116d00bd). AddSubgroup.map_map did not rewrite through `twistEnhanced` (def); used `(AddSubgroup.map_map _ _ _).trans`.
- SamePlace.AtkinLehner: builds (211c8484e). `S.finrank ▸ hcop` timed out at whnf; replaced by rw.
- SamePlace.FrobeniusSquare: builds (4810a1201). Vendored/Mathlib route of 7(a) worked directly: divisionUnit coordinates ⟨0,0,1,0⟩ by `ext <;> rfl`; square via mk_mul_mk; fallback through uniformizer_sq_value not needed.
- All #print axioms: only propext, Classical.choice, Quot.sound (torsionBy_eq_bot_congr: propext, Quot.sound). No sorry.

## Composition checks (scratch file outside the repo, `lake env lean`, not committed)
- pointForm_comp_map applied at f = ModelGeneric5.Wint h₅ htame h₂ (isExactDivisor_primePow) and φ = {atkinLevel with commutes' := atkinLevel_algebraMap}: hypothesis closed by `rfl`. So the levelCommRing statement of hf matches Wint.
- point and frobTwistSS elaborate at K = PMGeometry.ResidueAt v (DecidableEq by `open scoped Classical`, as in the tree).
- INTERFACE: types read only. PointW's `point` argument type = type of SamePlace.point at X.Point = ssPoint K ell N; sigmaEnhanced writes the block's class expression verbatim; same Pinned.Y0LevelPoints and resRing algebra. No change to the block needed.
- 6(c): vendored Algebra.IsSeparable.of_coprime_finrank_expChar applied directly; no fallback used.
- 7(b): OperatorComparison on the base matches What exists (fields hecke, atkin, frobenius; frobenius at Comparison.lean:103-104).
