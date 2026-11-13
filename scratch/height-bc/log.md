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
