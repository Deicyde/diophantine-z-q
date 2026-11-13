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
- OmegaBC.lean (= HBCPrefix (now also verbatim Final.lean 1150-1163, `OmegaBaseChange`) + hbc_proof +
  omega_proof.lean.part): VERIFIED (10:4x) `lake env lean` 0 errors, 0 sorry, 28 s; axioms standard for
  `mem_of_forall_locSub` (Step A: v ∈ N if ∀ maximal P ∃ d ∉ P, d•v ∈ N), `exists_act` (elements of
  𝒪_{𝒢,e(s)} act on ω through 𝒪_{S,s} = (𝓞_L)_s: t•(r•v) = p•v, t ∉ s, p ∉ s if r unit),
  `omegaAt_bc_local` (Step B: v ∈ (ω_{𝒢'})_{s'} ⇒ ∃ d ∉ s', d•v ∈ 𝓞_{L'}·π^*((ω_𝒢)_{bO s'}); proof:
  pullback_stalkGen at e'(s') ⇒ f'·w = G'^♯γ + u, u ∈ π^♯(I_{e(s)})𝒪; applying e'^♯ gives γ = 0),
  **`omegaBaseChange_of_localization : OmegaLocalization → OmegaBaseChange`**.
  New named Prop `OmegaLocalization` (one group model: ∀ s, ∀ v ∈ omegaAt s, ∃ d ∉ s, d•v ∈ omega).
- OmegaBC.lean regenerated (10:09): **`ZInQ.HeightBC.omegaBaseChange : OmegaBaseChange` PROVED** and
  **`omegaLocalization : OmegaLocalization`** (so the named Prop introduced above is discharged).
  VERIFIED: `lake env lean`, 0 errors, 0 sorry, 21 s; all 12 `#print axioms` [propext, Classical.choice,
  Quot.sound]; verbatim_check.py ALL OK (HodgeBCInjective, CotangentSpanBC, OmegaBaseChange).
  New lemmas: `omegaAt_sat` (u ∉ s, u•w ∈ omegaAt s ⇒ w ∈ omegaAt s; multiply generators by the unit
  G^♯(u)⁻¹), `omegaAt_full` (c•v ∈ omegaAt s₁ with c ≠ 0; affine chart around e(s₁), 𝒪_ξ = Γ(U)_𝔭,
  e^♯a vanishes on e⁻¹U by germ injectivity at the generic point), `omegaAt_open` (germ of I_{e(s)}
  extends over W ∋ e(s); e^♯F = 0 on e⁻¹W), `exists_mem_not_mem_of_sat` (Dedekind: nonzero ideal
  saturated at P₁ ≠ ⊥ contains P₁^n via the DVR R_{P₁}, so ⊄ P ≠ P₁), `finite_of_isClosed_not_genericPt`
  (closed Z ∌ η is finite: ⊆ minimal primes of a nonzero ideal).
- IntegrationBC.lean (assemble_int.py: verbatim infra-stalks HeightBCGlue.lean + stalk_tensor + cot_bc
  parts, ExtFrac, hbc_proof, omega_proof, verbatim height-bc PartE alias + g0-stablebc Main.part,
  int_final.lean.part): VERIFIED (10:11) `lake env lean` 0 errors, 26 s, no sorry (one doc-comment
  mention of the word); axioms standard for **`modelHeightBaseChange : ModelHeightBaseChange` (H4a)**,
  **`hodgeLineBaseChange : HodgeLineBaseChange`**, **`stableHeightBaseChange :
  G0StableBC.StableHeightBaseChange`** (g0-split piece 6), and for hodgeBCInjective, omegaBaseChange,
  omegaLocalization, cotangentSpanBC, uniformizationLiftAnalytic. verbatim_check.py ALL OK.
  FINDING: g0-stablebc's Main.part elaborates unchanged after `import Mathlib` (no breakage).
- Merged origin/main (e8eb4d61; no change under ZInQKernel/HDecomp, lakefile or manifest).
- ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean (same text as scratch ExtFrac.lean): `lake build
  ZInQKernel.Contrib.HodgeBC2.ExtFrac` OK (10:12); axioms of extFracEquiv, extFracBasis_apply standard.
- IntegrationH5.lean (assemble_h5.py: verbatim h5-glue H5Final.lean before its #print block +
  IntegrationBC body + int_h5.lean.part): VERIFIED (10:15) 0 errors, 40 s;
  `stableFaltingsHeight_eq_neron_of_N1N2` (h5-glue's H5, multi-field form, from leaves N1, N2 only)
  axioms standard. verbatim_check.py ALL OK.
