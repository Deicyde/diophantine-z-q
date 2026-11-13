# infra-smooth-dim results log

Base f90cf864 + merge origin/wip/mul-rigidity (60a480e0).

## Targets (verbatim statements)
- `LeafQM.AV.Pin.SmoothStalkDimOne` (scratch/curve-facts/CurveFacts.lean:539)
- `ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin` (scratch/hodge-lattice/HodgeLattice.lean:1144)
- mul-rigidity: its dimension input `QuasiFiniteEndSurjective` is already a theorem there (VERIFIED, docs/research/mul-rigidity.md row `quasiFiniteEndSurjective`); nothing left for this task.

## Compile log
- run1 MaxHeight.lean: `InfraSmoothDim.height_isMaximal_mvPolynomial` (k field, ι finite, M maximal in MvPolynomial ι k ⇒ M.height = Nat.card ι): 0 errors, axioms [propext, Classical.choice, Quot.sound] (VERIFIED)
- run2-5 CotQuot.lean: `InfraSmoothDim.spanFinrank_add_card_le` (local B Noetherian, C local, ψ : B →+* C with 𝔪_B·C = 𝔪_C, killing f : σ → 𝔪_B with linearly independent cotangent classes ⇒ spanFinrank 𝔪_C + |σ| ≤ spanFinrank 𝔪_B): 0 errors, standard axioms (VERIFIED)
- run6-12 StdSmoothLocal.lean §1-§2: `linearIndependent_relCot` (relations of a submersive presentation have κ-linearly independent classes in 𝔪/𝔪² of k[x]_M, M ⊇ ker maximal), via `coeffs_mem_of_sum_mem_sq` (derivative + Jacobian mod M) and `sum_mem_sq_of_cotangent`: compiles. (One monolithic version hit a kernel deterministic timeout; splitting into three lemmas fixed it.)
- run13-19 StdSmoothLocal.lean §3: `ringKrullDim_and_spanFinrank_localization` (P : SubmersivePresentation k S ι σ, k field, 𝔪 maximal ⇒ ringKrullDim S_𝔪 = P.dimension ∧ spanFinrank 𝔪S_𝔪 = P.dimension): 0 errors, standard axioms (VERIFIED). Uses Mathlib's Krull height theorem (`Ideal.height_le_height_add_spanFinrank_of_le`), regularity of k[x] (`MvPolynomial.isRegularRing_of_isRegularRing`), `ringKrullDim_le_spanFinrank_maximalIdeal`.
