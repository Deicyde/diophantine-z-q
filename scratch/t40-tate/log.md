# t40-tate results log

Target: `ZInQ.RLeaf.TateCuspLaurent` (ZInQKernel/Contrib/RLeaf/X1RationalCusp.lean).

## Plan (2026-11-13 09:30)
- Split: `TateLaurentTorsion` (exists elliptic W/ℚ((t)), j ∉ ℚ[[t]], point of exact order N, N ≥ 2)
  ⇒ `TateCuspLaurent` (algebraic glue: φ: ℚ(j) → ℚ((t)), j ↦ j(W); W ≅ E_j^φ over the algebraic
  closure with L-rational x-transform (char 0, j ≠ 0,1728); torsion counting (T36) to lift the
  point back to `EjBar`).
- `TateLaurentTorsion` from Tau Ceti's Tate uniformization hom (tc-main
  TateCurve/Homomorphism.lean; closure 69 modules / 16k lines, 57 not vendored, 22 main/nov01-only)
  plus a complete ultrametric NormedField structure on ℚ((t)).

## Results
- 09:32 TateCuspGlue.lean with `def TateLaurentTorsion` compiles (lake env lean). VERIFIED.
- 10:15 Backport of tc-main (4d91513e) TateCurve.Homomorphism closure: 57 full modules under Backport/ + 5 extras files (decls absent from vendored oct16 versions); lake build ...TateCurve.Homomorphism succeeds. VERIFIED.
- 10:35 TateCuspTorsion.lean: `ZInQ.RLeaf.TateCuspTorsion.tateLaurentTorsion : TateLaurentTorsion` compiles, axioms [propext, Classical.choice, Quot.sound]. VERIFIED (lake env lean). Normed field on ℚ((t)) = Valued.toNormedField with RankOne hom' = toNNReal 2 ∘ embedding.
- 09:50 (host clock) TateCuspGlue.lean: `ZInQ.RLeaf.tateCuspLaurent_of_tateLaurentTorsion : TateLaurentTorsion → TateCuspLaurent`, axioms [propext, Classical.choice, Quot.sound]. VERIFIED (lake env lean).
- 09:53 TateCusp.lean: `ZInQ.RLeaf.tateCuspLaurent : TateCuspLaurent`, `x1RationalCusp_of_igusaTransitive : IgusaTransitive → X1Belyi.X1RationalCusp`, `x1ConstantField_of_igusaTransitive : IgusaTransitive → X1Belyi.X1ConstantField`; `lake build ZInQKernel.Contrib.RLeaf.TateCusp` exit 0, all three axioms [propext, Classical.choice, Quot.sound]. VERIFIED (build log scratch/t40-tate/build-tatecusp.txt).
  (Earlier log timestamps 10:15/10:35 were estimates, not the host clock; the host clock read 09:26 at start.)
- diffcheck2: counts {'IDENT': 1644, 'NOTE-ONLY': 0, 'MOD-NOTED': 35, 'MOD-UNNOTED': 0, 'NOPROV': 110, 'NOSRC': 0}. VERIFIED. NOTICE: t40-tate entries added (Source bullet + Location paragraph).
- (host ~10:30) t40-igusa reduced IgusaTransitive ↔ X0Transitive ∧ TateMuN (IgusaX0.lean) and added per-level `TateMuNAt N Ω` + `tateMuN_of_at` (IgusaLocal.lean) at my request. Agreed by message: I prove `ZInQ.RLeaf.tateMuN : TateMuN` in TateCuspMuN.lean; t40-igusa writes T40.lean.
- TateCuspMuN.lean: generic K((t)) normed field (rankOneK), `valuation_mapRingHom`/`norm_mapRingHom` (coefficient maps along injective field maps are isometric), `continuous_mapRingHom`, transport lemmas, level-N setup (K = CyclotomicField N ℚ, Ω = AlgebraicClosure K((t)), Qj-algebra j ↦ j(E_t), σ_g coefficientwise, τ_g = IsAlgClosure.equivOfEquiv) compile. First full attempt at `tateMuNAt_level`: elaborates, but kernel deterministic timeout (200000 heartbeats).
- Kernel deterministic timeouts in the concrete K((t)) version of tateMuNAt were bisected to rewrites (map_nsmul on the Additive quotient, map_zero/addOrderOf_zero on points, the units-power from a generic lemma) whose instance paths on the concrete field `CyclotomicField N ℚ ((t))` differ from the generic `[NormedField F]` paths. Fix (VERIFIED): state the whole argument for an arbitrary complete ultrametric `F` with isometric `incl : ℚ((t)) → F` (`tateMuNAt_of_unit`), with `Ω = ΩF F incl` a def-copy of `AlgebraicClosure F` carrying the instance `Algebra Qj Ω` (j ↦ j(E_t)); specialize to `F = K((t))` (`tateMuNAt_of_root`) and `K = CyclotomicField N ℚ` (`galN`, via `autEquivPow`).
- 11:04 TateCuspMuN.lean: `ZInQ.RLeaf.tateMuN : TateMuN` (TateMuN of t40-igusa's IgusaX0.lean, via its `tateMuN_of_at`), axioms [propext, Classical.choice, Quot.sound]. VERIFIED: `lake build ZInQKernel.Contrib.RLeaf.TateCuspMuN ZInQKernel.Contrib.RLeaf.TateCusp` "Build completed successfully (9394 jobs)" (scratch/t40-tate/build-tatecuspmun.txt). Messaged t40-igusa (it writes T40.lean: T40 from X0Transitive alone).
