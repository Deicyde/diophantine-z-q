# hodge-lattice results log

- 2026-11-12 (22:58) `lake build ZInQKernel.HDecomp.Faltings.Models`: OK (1m51).
- (commit 23:05) scratch/hodge-lattice/HodgeLattice.lean compiles (`lake env lean`), no errors; one
  deprecation warning (TensorProduct.induction_on). VERIFIED.
  - `alt_eq_smulRight`: top-degree alternating map on R^g with values in N equals det · F(e).
  - `exists_clear`: denominators in K ⊗_{O_K} M (via IsLocalizedModule from isBaseChange).
  - `tmul_ιMulti_mem_span`: 1 ⊗ ιMulti v ∈ K·(1 ⊗ ιMulti w).
  - `hodgeLattice_of_lattice`: ω FG, rank_K (K⊗M) = g, ω spans K⊗M ⇒ finrank_K (K ⊗ ⋀^g M) = 1
    ∧ ∃ s ∈ detLat ω g, s ≠ 0 ∧ secIndex ≠ 0.
  - `hodgeLatticeTheorem_of : OmegaFG → CotangentRank → OmegaSpans → HodgeLatticeTheorem`.
  - axioms of both: [propext, Classical.choice, Quot.sound].
- (commit 23:08) §3-§4 added, file compiles, no errors (deprecation warnings only). VERIFIED.
  - `exists_finset_cover`, `fg_iInf_of_local`, `exists_smul_mem_iInf_of_local` (local-to-global over Spec R).
  - `OmegaLocal` (Prop): near each s ∈ Spec 𝓞_L, on D(a) ∋ s, one f.g. N ⊆ cot spanning over L with
    N ≤ omegaAt s' and omegaAt s' ⊆ loc_{s'} N for s' ∈ D(a).
  - `omegaFG_of_omegaLocal`, `omegaSpans_of_omegaLocal`,
    `hodgeLatticeTheorem_of_local : OmegaLocal → CotangentRank → HodgeLatticeTheorem`; axioms standard.
- (commit 23:22) scratch/hodge-lattice/Local.lean compiles, 0 errors (linter warnings only). VERIFIED.
  `omegaLocal : OmegaLocal` PROVED, axioms [propext, Classical.choice, Quot.sound].
  Ingredients: affine chart U ∋ e(s) (isBasis_affineOpens), basic open D(a) ⊆ e⁻¹U,
  Γ(U) noetherian (LocallyOfFiniteType.isLocallyNoetherian, component_noetherian),
  I = ker(e.app U) f.g., N = 𝓞_L-span{d(germ_ξ i) : i ∈ gens I}; stalks on U are fractions
  (IsAffineOpen.isLocalization_stalk); germ_injective_of_isIntegral on Spec 𝓞_L;
  residue lemma (stalk of Spec 𝓞_L at s' is a localization; stalkSpecializes_stalkMap).
  Fullness of N from (C) at the generic point plus `omegaAt_genericPt`.
  ClaimA.lean: dCls_mem_omegaAt alone (also inside Local.lean).
- (commit 23:24) Local.lean merged into HodgeLattice.lean §5 (Local.lean, ClaimA.lean removed). Compiles,
  0 errors. `hodgeLatticeTheorem_of_cotangentRank : CotangentRank → HodgeLatticeTheorem`,
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- (commit 23:28) §6 added; file compiles, 0 errors. VERIFIED.
  - `isUnit_structMap` (c ≠ 0 ⇒ structMap c unit), `spec_genericPt`.
  - `rank_tensor_cotangent : rank_L (L ⊗_{𝓞_L} cot) = rank_{κ(ξ)} (CotangentSpace 𝒪_{𝒢,ξ})`
    (κ(ξ) is a fraction field of 𝓞_L via residue ∘ structMap; IsBaseChange of id).
  - `TangentDim`, `RegularOrigin` (IsRegularLocalRing 𝒪_{𝒢,ξ}), `DimOrigin` (ringKrullDim 𝒪_{𝒢,ξ} = dim A).
  - `cotangentRank_of_tangentDim`, `tangentDim_of_regular`,
    `hodgeLatticeTheorem_of_regular : RegularOrigin → DimOrigin → HodgeLatticeTheorem`,
    axioms [propext, Classical.choice, Quot.sound].
- (commit 23:31) §7: `detLat_fg`, `hodgeLattice_lattice_of_regular` (ω_𝒢 FG, detLattice FG, span_L detLattice = ⊤).
  File compiles, 0 errors, no `sorry` in the file; all 7 #print axioms standard. VERIFIED.
- (commit ~23:37) §8: `originPt`, `OriginStalkIso`, `RegularAtOrigin`, `DimAtOrigin`, `DimBaseChange`;
  `regularOrigin_of`, `dimOrigin_of`, `hodgeLatticeTheorem_of_abVar`
  (OriginStalkIso → RegularAtOrigin → DimAtOrigin → DimBaseChange → HodgeLatticeTheorem).
  0 errors; axioms standard. VERIFIED.
