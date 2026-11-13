# h5-glue results log

Base: wip/h5-glue at 883c4ddf, merged origin/wip/h5-neron (b7c1dc21) for scratch/h5-neron and
docs/research/h5-neron.md.

## 1. Glue H4b `GroupModelBaseChangeExists` — PROVED (compiled ~01:52, scratch/h5-glue/BaseChange.lean)
- `genBC` (generic-fibre identification of a base change, for abstract morphisms
  a,b,c,d,k,k' with a≫b = c≫d, c≫k = k') and `genBC_isMonHom` (it is a monoid morphism):
  compiled, axioms [propext, Classical.choice, Quot.sound].
- `GroupModel.baseChange L L' 𝒢 : GroupModel A L'` and `groupModelBaseChangeExists :
  GroupModelBaseChangeExists` (statement copied verbatim from h5-neron): compiled, axioms
  [propext, Classical.choice, Quot.sound]. Whole file ~7 s elaboration.
- FINDING: h5-neron's kernel deterministic timeout disappears when the IsMonHom proof is done
  over abstract morphisms and instantiated afterwards (the kernel never unfolds the concrete
  Spec.map/algebraMap (𝓞 L) L terms).

## 2. NeronModelMinimal reduced to one glue `HeightAntitone` (compiled ~01:56, scratch/h5-glue/Minimal.lean)
- `isMonHom_of_map` (general: a strong monoidal F injective on Hom(𝟙,Y), Hom(X⊗X,Y) reflects
  IsMonHom): compiled.
- `neron_lift_isMonHom`: the Néron comparison map 𝒢 → 𝒩 is IsMonHom and its generic fibre
  F.map f is an iso: compiled.
- `HeightAntitone` (glue, STATED): f : 𝒢.G ⟶ 𝒩.G, IsMonHom f, IsIso (F.map f) ⇒ 𝒩.height ≤ 𝒢.height.
- `neronModelMinimal_of_heightAntitone : HeightAntitone → NeronModelMinimal`: compiled.
  All three #print axioms: [propext, Classical.choice, Quot.sound].

## 3. Open subgroup models are generic isomorphisms — PROVED (compiled ~01:59, scratch/h5-glue/OpenSub.lean)
- `isOpenImmersion_pullback_map`: Over.pullback j sends open immersions to open immersions
  (IsPullback.of_bot pasting + MorphismProperty.of_isPullback).
- `isIso_of_openImmersion_self`: an open immersion B.X ⟶ B.X over Spec L of an AbVar is an iso
  (universally closed via proper + separated; image clopen nonempty in the irreducible B.X —
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton; isIso_iff_isOpenImmersion_and_surjective).
- `genericIso_of_openImmersion`: f : 𝒰.G ⟶ 𝒢.G with f.left an open immersion ⇒ IsIso (F.map f).
  All three: axioms [propext, Classical.choice, Quot.sound]. This is the "on generic fibres it is an
  isomorphism" clause of h5-neron's OpenSubgroupHeight docstring, now a Lean proof.

## 4. Complex points — PROVED (compiled ~02:00, scratch/h5-glue/Pts.lean)
- `ptCIso`, `ptsEquiv` (𝒢.Pts τ ≃ L-points of the generic fibre, via Over.mapPullbackAdj),
  `ptsEquiv_comp`, `pts_comp_bijective`: if F.map f is an iso, p ↦ p ≫ f is a bijection
  𝒢.Pts τ → 𝒩.Pts τ. Axioms [propext, Classical.choice, Quot.sound].

## 5. Combined file scratch/h5-glue/H5Glue.lean — COMPILED ~02:01 (no errors; 12 #print axioms,
## all [propext, Classical.choice, Quot.sound])
- §1-§4 as above; §5: N1, N2, IsOpenSubgroupModel, ModelHeightBaseChange, OpenSubgroupHeight,
  compositum copied verbatim from h5-neron.
- `OpenImmersionHeightLe` (glue, STATED): open-immersion homomorphism f : 𝒰 → 𝒢 with generic iso ⇒
  𝒰.height ≤ 𝒢.height.
- `openSubgroupHeight_of : HeightAntitone → OpenImmersionHeightLe → OpenSubgroupHeight`.
- `stableFaltingsHeight_eq_neron_all (hN1 hN2 hA hO hbc)`: H5 in the multi-field form R19-R21 need,
  from leaves N1, N2 and glue HeightAntitone, OpenImmersionHeightLe, ModelHeightBaseChange only
  (h5-neron's version needed six glue hypotheses incl. NeronModelMinimal, GroupModelBaseChangeExists).

## 6. Independent model review of H5Glue.lean (read-only subagent, ~02:06)
- No statement false or vacuous; copied statements match H5Neron.lean token for token.
- PROBLEM (documentation): `HeightAntitone`'s docstring omits an input. Building a metrization of
  𝒩 needs `HodgeData.isLattice` for 𝒩.detLattice g. Finite secIndex follows from 𝒢's lattice
  (sub-𝓞-module of a rank-one lattice), but NONVANISHING of detLattice_𝒩 (ω_𝒩 of full generic rank)
  does not follow from f* (only ω_𝒩 ↪ ω_𝒢). Needs the full-rank half of HodgeLatticeTheorem for 𝒩
  (true: 𝒩 smooth). Same observation made independently before the review.
  → NeronModelMinimal is true but its proof needs (part of) HodgeLatticeTheorem: it is not pure glue
    over the mapping property (corrects h5-neron finding (d)).
- `OpenImmersionHeightLe`: TRUE with no extra input (ω_𝒰 = f*ω_𝒢; gives equality).

## 7. Local ring at ξ along a generic isomorphism — PROVED (compiled ~02:07, scratch/h5-glue/Stalk.lean)
- `map_genericUnit`: IsMonHom f ⇒ f.left 𝒢.genericUnit = 𝒩.genericUnit.
- `stalkIso_of_genericIso`: IsIso (F.map f) ⇒ IsIso (f.left.stalkMap 𝒢.genericUnit).
- Uses hodge-lattice's `genericFibreStalkIso`, `fst_genericFibreUnit` (copied verbatim, re-compiled).
  Axioms [propext, Classical.choice, Quot.sound].

## 8. Additivity with reduced glue — PROVED (compiled ~02:09, scratch/h5-glue/Additivity.lean)
- `stableFaltingsHeight_add_le_of_heightAntitone (hN1 hA hH)`: h(A)+h(B) ≤ h(C) for C ≅ A×B from
  N1, HeightAntitone, ProductModelHeight (h5-neron's product material copied verbatim).

## 9. Archimedean transport — PROVED (compiled ~02:11 / ~02:16, Analytic.lean, JacDet.lean)
- `evalAt_comp`, `dom_comp` (rfl), `isAnalyticUniformization_comp`: f MonHom + generic iso ⇒
  z ↦ Φ z ≫ f is an analytic uniformization of 𝒩 with the same Λ.
- `evalAt_res`, `ptC_hom_apply` (Spec ℂ → Spec 𝓞_L hits the generic point), `one_mem_dom`,
  `map_zero_of_hom`, `germAlong_comp_eventuallyEq` (germs along Φ≫f and along Φ agree near 0 for any
  φ compatible with f^* on sections), `jacDet_comp_map`: jacDet (Φ≫f) t = jacDet Φ (φ∘t).
  All axioms [propext, Classical.choice, Quot.sound].
- `genMap 𝒢 𝒩 f : 𝒩.genStalk ⟶ 𝒢.genStalk` (stalkSpecializes ≫ stalkMap), `genMap_germ` (f^* on
  germs), `jacDet_comp_genMap`: compiled ~02:18, axioms standard.
- `genMap_mem_maximalIdeal` (genMap is local), `genMap_structMap` (compatible with 𝓞_L),
  `cotMap 𝒢 𝒩 f : 𝒩.cotangent →ₗ[𝓞 L] 𝒢.cotangent` (f^* on 𝔪_ξ/𝔪_ξ²), `cotMap_dCls` (rfl):
  compiled ~02:20, axioms standard.
- HeightAntitone docstring updated with the HodgeLatticeTheorem dependency in Minimal/H5Glue/Additivity; all three recompiled (standard axioms).

## 10. Step R1 — PROVED (compiled ~02:21, JacDet.lean)
- `unitSection_comp`, `stalkSpecializes_stalkSpecializes_apply`, `stalkSpecializes_self_apply`,
  `cotMap_omegaAt` (f^* maps (ω_𝒩)_s into (ω_𝒢)_s at every s), `cotMap_omega`: f^*(ω_𝒩) ⊆ ω_𝒢 for any
  homomorphism f (no generic-iso hypothesis needed). Axioms standard.

## 11. Step R2 (lattice part) — PROVED (compiled ~02:23, JacDet.lean)
- `hodgeMap 𝒢 𝒩 f g := (exteriorPower.map g cotMap).baseChange L : 𝒩.hodgeSpace g →ₗ[L] 𝒢.hodgeSpace g`,
  `hodgeMap_wedge`, `hodgeMap_detLattice` (maps ⋀^g ω_𝒩 into ⋀^g ω_𝒢), `hodgeMap_wedgeGerm`
  (wedge t ↦ wedge (genMap ∘ t)). Axioms standard. Bijectivity of hodgeMap NOT proved.

## 12. Assembly: HeightAntitone from two algebraic glue statements — PROVED (compiled ~02:25, JacDet.lean)
- `secIndex_ne_zero_of_mem` (in a Hodge line every nonzero lattice vector has finite index),
  `secIndex_le_of_map` (indices along an injective map into a lattice), `pullHodge` (pull back
  HodgeData along an injective L-linear map onto a new lattice), `modelHeight_pullHodge_le`.
- `HodgeMapBijective` (glue, STATED): hodgeMap bijective for a generic iso f.
- `HodgeLatticeNonzero` (glue, STATED): finrank_L (𝒩.hodgeSpace g) = 1 ⇒ ∃ v ∈ 𝒩.detLattice g, v ≠ 0.
- `heightAntitone_of : HodgeMapBijective → HodgeLatticeNonzero → HeightAntitone` — axioms standard.
  (HeightAntitone restated verbatim as in Minimal.lean.)

## 13. HodgeMapBijective — PROVED; HeightAntitone ⇐ HodgeLatticeNonzero (compiled ~02:28, JacDet.lean)
- hodge-lattice's §9-§10 lemmas and `stalkIso_of_genericIso` copied into JacDet.lean.
- `isIso_genMap`, `cotMap_bijective` (f^* on 𝔪/𝔪² bijective: genMap a local ring iso, comap of 𝔪²),
  `baseChange_map_bijective`, `hodgeMapBijective : HodgeMapBijective`,
  `heightAntitone_of_hodgeLatticeNonzero : HodgeLatticeNonzero → HeightAntitone`. Axioms standard.

## 14. HodgeLatticeNonzero from OmegaSpans — PROVED (compiled ~02:30, JacDet.lean)
- `OmegaSpans` (copied verbatim from hodge-lattice §2, where it is PROVED: omegaSpans_of_omegaLocal omegaLocal).
- `exists_smul_mem_omega`, `hodgeLatticeNonzero_of_omegaSpans`, `heightAntitone_of_omegaSpans`. Axioms standard.

## 15. NeronModelMinimal and HeightAntitone — PROVED (compiled ~02:31, scratch/h5-glue/NeronMinimal.lean)
- Self-contained file: hodge-lattice §1-§5 copied verbatim (for `omegaLocal`, `omegaSpans_of_omegaLocal`)
  + JacDet.lean + Minimal.lean.
- `omegaSpans : OmegaSpans`, `heightAntitone : HeightAntitone`,
  `neronModelMinimal : ZInQ.DefFaltings.NeronModelMinimal` (the project's Prop from Height.lean).
  #print axioms: [propext, Classical.choice, Quot.sound]; no sorry/axiom in the file. Compile ~13 s.
- REVISES finding (a): the nonvanishing of ⋀^g ω_𝒩 needed for HodgeData.isLattice follows from
  OmegaSpans (coherence of e*Ω¹, proved by hodge-lattice without dimension theory) together with the
  transported finrank 1; no rank/dimension input (TangentDimAtOrigin, DimBaseChange) is needed.
  So h5-neron's (d) "NeronModelMinimal is glue" is CORRECT, and it is now proved.

## 16. Final combined file scratch/h5-glue/H5Final.lean — COMPILED ~02:32 (0 errors; 8 #print axioms,
## all [propext, Classical.choice, Quot.sound]; ~2360 lines, ~18 s)
- = NeronMinimal.lean + H5Glue.lean §1 (H4b), §3 (open subgroups), §5 (copied statements, reduction)
  + Additivity.lean's h5-neron product material.
- `stableFaltingsHeight_eq_neron_all (hN1 hN2 hO hbc)`: H5 multi-field form from leaves N1, N2 and glue
  OpenImmersionHeightLe, ModelHeightBaseChange ONLY.
- `stableFaltingsHeight_add_le_of_productModelHeight (hN1 hH)`: additivity from N1 and P2 only.
