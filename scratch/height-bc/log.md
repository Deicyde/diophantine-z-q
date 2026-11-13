# height-bc results log

- Build: `lake build ZInQKernel.HDecomp.Faltings.Leaves` (1m47, 04:10).
- `HeightBC.lean` Part A = verbatim copies (h5-glue `IsBaseChangeOf`, `ModelHeightBaseChange`;
  g0-stablebc Main.part lines 46-56 and 240-500: `ModelHeightBaseChangeLE`, ArakelovBC section,
  `MetrizationBaseChange`, `HodgeLineBaseChange`, `metrizationBaseChange_of_hodgeLine`) re-elaborated
  over the kernel's `ZInQ.DefFaltings` objects (g0-stablebc had them over its Defs.part copy) +
  new descent half.
- run2 (04:16): `lake env lean scratch/height-bc/HeightBC.lean`: 0 errors, no sorry, 52 s.
  VERIFIED: `modelHeightBaseChange_of_descent : HodgeLineBaseChangeDescent → ModelHeightBaseChange`
  (H4a `=`, statement verbatim), axioms [propext, Classical.choice, Quot.sound].
  New proved pieces: `exists_comp_eq` (σ extends to L'), `exists_ringOfIntegers_of_algebraMap`,
  `secIndex_ne_zero_of_baseChange` (finite index descends), `modelHeightBaseChangeGE_of_descent`
  (choose τ' above σ maximizing log‖ψw‖²_τ'; max ≥ average via `sum_embeddings_comp`),
  `hodgeLineBaseChange_of_descent`.
- FINDING: `HodgeLineBaseChange` alone does not give H4a `≥`: it lacks (i) the converse line clause
  (finrank L' V' = 1 → finrank L V = 1; an injective semilinear ψ does not bound dim_L V) and
  (ii) descent of uniformizations from 𝒢'(ℂ)_τ' to 𝒢(ℂ)_{τ'|L}. `HodgeLineBaseChangeDescent` adds
  exactly these two clauses (same ψ).
- Natural.lean (04:53): construction of the natural map compiles (0 errors, no sorry):
  `bO_genericPt`, `bO_appTop`, `IsMonBC` (IsBaseChangeOf ↔ ∃ e, IsMonBC e), `bcProj` (π = e.hom.left ≫ fst),
  `bcProj_w`, `bcProj_unit` (e'∘π = bO∘e, from IsMonHom e.hom and `obj.η_def`), `bcProj_genericUnit` (π ξ' = ξ),
  `bcMap` (𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}), `bcMap_germ`, `bcMap_mem_maximalIdeal`, `bcMap_structMap`,
  `bcCot` (semilinear over 𝓞_L → 𝓞_{L'}), `bcAlt`, `bcExt` (⋀^g π^*, via compHom restriction of scalars),
  `bcHodge` (ψ = L' ⊗ ⋀^g π^*, via `TensorProduct.liftAddHom`), `bcHodge_smul` (L-semilinear),
  `bcHodge_wedge` (ψ(wedge f) = wedge'(π^* f)).
- Final.lean (04:35) = HeightBC.lean + Natural.lean + Part C: 0 errors, no sorry, ~12-60 s.
  VERIFIED (axioms [propext, Classical.choice, Quot.sound] for each):
  `hodgeLineBaseChangeDescent_of_glue`, `modelHeightBaseChange_of_glue`, `hodgeLineBaseChange_of_glue`:
  H4a and HodgeLineBaseChange (both verbatim) from six glue Props over the natural map:
  HodgeBCInjective, DetLatticeBC, PtsBaseChangeMul, PtsBaseChangeBij, UniformizationLift,
  JacobianPullbackSpan. Proved along the way: `bcPts` (β p' = π ∘ p'), `evalAt_bcPts`, `dom_bcPts` (rfl),
  `germAlong_bcPts_eventuallyEq`, `jacDet_bcPts` (jacDet (β∘Φ') f = jacDet' Φ' (π^* f)),
  `isAnalyticUniformization_bcPts` (descent of uniformizations from BC-pts-mul, BC-pts-bij).
- Final.lean (04:45): `ptsBaseChangeBij : PtsBaseChangeBij` and `ptsBaseChangeMul : PtsBaseChangeMul`
  PROVED (pullback universal property; `MonObj.mul_comp` + `Over.μ_pullback_left_fst_fst/_fst_snd`).
  VERIFIED: `modelHeightBaseChange_of_four`, `hodgeLineBaseChange_of_four` (H4a and HodgeLineBaseChange,
  verbatim, from HodgeBCInjective, DetLatticeBC, UniformizationLift, JacobianPullbackSpan) and
  `modelHeightBaseChangeGE_of_two` (H4a `≥` from HodgeBCInjective, DetLatticeBC only), all axioms
  [propext, Classical.choice, Quot.sound]; 0 errors, no sorry (grep: 0 occurrences), 12 s.
- Final.lean (~05:00): half of BC-lat proved (`bcCot_omegaAt`, `bcCot_omega`: π^*(ω_𝒢) ⊆ ω_{𝒢'} at every
  point of Spec 𝓞_{L'}; `bcHodge_detLattice`, `span_bcHodge_le`); general lemma `multilinear_mem_span`;
  new glue `OmegaBaseChange` (ω_{𝒢'} ≤ 𝓞_{L'}·π^*(ω_𝒢)) and `detLatticeBC_of_omega`.
  VERIFIED: `modelHeightBaseChange_of_main`, `hodgeLineBaseChange_of_main` (from HodgeBCInjective,
  OmegaBaseChange, UniformizationLift, JacobianPullbackSpan), `modelHeightBaseChangeGE_of_main`
  (from HodgeBCInjective, OmegaBaseChange). 14 `#print axioms`, all [propext, Classical.choice, Quot.sound];
  0 errors, 16 s.
- Read-only model review (subagent, no Lean run) of HodgeBCInjective, DetLatticeBC, UniformizationLift,
  JacobianPullbackSpan, HodgeLineBaseChangeDescent: all TRUE for every g, none vacuous. Docstring
  points: "the natural map ψ" vs ∃ψ in copied Props; BC-span needs the spanning fact V' = L'·bcCot(V)
  (not part of HodgeBCInjective); BC-lift's real step is continuity of β∘Φ' + L'-defined opens;
  EGA locators (base change of Ω¹: IV 16.4.5? conormal ≅ e*Ω¹: IV 17.2.5?) UNVERIFIED; stale headers.
- H5WithBC.lean (04:51) = scratch/h5-glue/H5Final.lean (verbatim, its #print lines dropped) + Final.lean
  body + Part D: 0 errors, 1m10s. `h5_modelHeightBaseChange_iff : ZInQ.H5Glue.ModelHeightBaseChange ↔
  ModelHeightBaseChange := Iff.rfl`; `stableFaltingsHeight_eq_neron_of_main` (h5-glue's H5, multi-field form,
  from leaves N1, N2 and HodgeBCInjective, OmegaBaseChange, UniformizationLift, JacobianPullbackSpan):
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
