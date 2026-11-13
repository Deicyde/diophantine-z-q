# hodge-bc2 results log

- Merged origin/wip/infra-stalks (b691f922).
- ExtFrac.lean (Mathlib-only): `extFracEquiv : ⋀[K]^n M ≃ₗ[K] K ⊗[R] ⋀[R]^n M` (R domain, K = Frac R,
  M a K-space), `extFracEquiv_ιMulti`, `extFracBasis` (basis `1 ⊗ ιMulti_family R n b` from a K-basis b),
  `extFracBasis_apply`, `smul_eq_of_frac`. VERIFIED: `lake env lean`, 0 errors, 6 s (09:45).
- HodgeBCInjective.lean (assemble.py: Leaves + Mathlib imports; verbatim infra-stalks
  CotangentBaseChange.lean body, ExtFrac body, verbatim Final.lean 29-34, 590-856, 1747-1757, 1453-1465,
  verbatim infra-stalks bc_proof.lean.part; new hbc_proof.lean.part):
  **`ZInQ.HeightBC.hodgeBCInjective : HodgeBCInjective` PROVED.** VERIFIED (09:49): `lake env lean`,
  0 errors, no sorry, 21 s; axioms [propext, Classical.choice, Quot.sound] (also for extFracEquiv,
  extFracBasis_apply, cotangentSpanBC, bcCot_core, bcCotBasis_apply). verbatim_check.py: ALL OK.
  Ingredients: `φL : L → 𝒪_{𝒢,ξ}` via `L ≅ κ(η)` (IsLocalization.algEquiv) and the stalk map at the
  generic point; `cotL` (L-space structure on ω, compHom), `bcCot_smulL` (π^* L-semilinear, ring-hom
  ext on 𝓞_L); `bcCot_core` (cotangent_baseChange_injective at z = e(ξ'), s = η, y = η', transported
  along the iso stalk map of e, + Module.Flat.linearIndependent_one_tmul over the field κ(η));
  `bcCotBasis` (π^*∘b is an L'-basis; span from cotangentSpanBC); `extFracBasis` both sides,
  ψ(B s) = B' s; finrank = Nat.card (powersetCard I g) on both sides.
