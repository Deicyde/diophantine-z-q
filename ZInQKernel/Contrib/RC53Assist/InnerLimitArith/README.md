# Inner-limit arithmetic contributions: classification of the contracts

This directory contains the arithmetic side of the inner limit along moving derivative primes in
the proof of Theorem 5.3 (manuscript lines 4391–4451, 4748–4907, 4976–5135). The classification
below follows the independent review of the first round and states which declarations are
genuine producers and which are conditional adapters. A conditional adapter proves its conclusion
from inputs that are not themselves produced here; such inputs remain open obligations and must
not be counted as discharged arithmetic.

## Genuine producers (no arithmetic input beyond the stated prints)

(Reclassified after a second independent review, 2026-11-18.)

* Actual continuous cochains and their evaluation, cocycle and coboundary identities
  (`evalOne`, `evalOne_mul`, `evalOne_d_zero`, `evalTwo_d`), tame coordinates of actual
  one-cocycles (`tameCoord`, `tameCoordH1`), the actual unramified condition in tame coordinates
  (`tameCoord_urCondCocycle`), localization at a prime outside `S` (`tameCoord_localizeCocycle`).
* Moving labels from any sequence of primes outside `S` (`MovingLabel.ofPrimes`), and the limit
  Frobenius in the compact group `G_{K,S}` (`MovingLabel.limitFrob`).
* Actual derivative primes by finite Chebotarev at every stage (`DerivativePrimes`,
  `exists_derivativePrimes`), with `ℓ_i ≡ −1 mod 2^i` (`DerivativePrimes.ell_mod`), the
  determinant of the conjugation (`det_tateMatrix_conj`), and convergence of the rational
  Frobenius elements (`DerivativePrimes.tendsto_frob`).
* The conjugation in the coefficient basis: `tateSEquiv`, `rhoK`, `rhoKMatrix`, `conjMatrixK`,
  `conjTate_eq_rhoK`, `conjMatrix_eq_conjMatrixK` (the fibre duality's `conjMatrix` is the
  specialization of `ρ_T(τ)`), `det_conjMatrixK`, `conjMatrixK_sq`.
* Flatness and freeness of the actual stage cochain and Selmer cochain modules
  (`StageFlat.lean`).
* `StageInputs.lean`, from the prints named there: chain-level reciprocity of the trace on the
  compact cone (`trace_reciprocity`, `trace_localization_of_cocycle`); Nekovář's global duality at
  the stage `A_i` for `M_i`, `M_i(α⁻¹)` and the Weil pairing (`stageGlobalDuality`,
  `exists_stageTrace`, from Nekovář 5.4.1 and 5.4.3, as imported).

## Conditional adapters (inputs are open obligations)

* `StageInputs.lean`: finiteness of the cohomology of the actual Selmer complexes with finite
  coefficients (`galoisSelmerCohomologyFinite_of_prints`, `stageSelmerCohomologyFinite`, from
  Milne, ADT I, Theorem 2.1 and Corollary 4.15) is conditional on finiteness of the cohomology
  of the specified local conditions; `stageSelmerDuality` keeps the orthogonality of the old
  conditions as an input. `LocalDegreeTwoCoordinate` is an isomorphism-witness contract, and
  `LocalDegreeTwoNormalized` alone does not certify a coordinate (an independent review compiled
  a normalized map on a trivial group that kills no coboundary): the actual continuous
  characters and the normalized cup cocycles must be bound, as the separate normalized
  coordinate does.
* `ArithLabel.lean`: `CompatibleArithmeticLabel` is a bundle; defining it constructs no
  inhabitant, and `residue_size` repackages its `above` and `inert` fields. The derived fields
  (`htriv`, the realized derivative matrices with `J = conjMatrix`) are genuine consequences
  of the bundle. Inhabitants are built by the separate constructors from actual finite-stage
  kernel elements (the Frobenius match from inert primes, the character condition by a refined
  Chebotarev selection, and the stage primes as the inert primes above the selected rational
  primes); detection of prescribed classes and the evaluation transport (5.4) remain open.

* `realizedDerivative`, `realizedDerivativeK`, `RealizedLabel.derivative`: the input `htriv`
  (the Frobenius of the stage prime acts trivially on `𝕋 / I_i 𝕋`) is equivalent to the
  stage-matrix congruence `phi_congr`; it is assumed, not derived. `realizedDerivativeK_of_match`
  replaces it by `FrobeniusMatchesLabel` and the character constraint, which are still inputs.
  Not bound by these constructors: `W = E.baseChange K`, inertness of the stage primes, residue
  size `(ℓ_i)^2` at the stage prime, and the relation between the two Frobenius families.
* `DegreeOneRealization`, `SelmerRealization`: witness contracts, not model identifications.
  Zero witnesses satisfy them, the cocycle map need not be injective, and with the cofinite and
  inertia conditions they force the relaxed image into the finite plane. They must not be used
  as the retained model comparison with the unchanged old conditions and the class/functional
  maps, which remains open.
* `detectedLimitNonquadStep`, `realizedFibreLimitNonquadStep`, `retainedNonquadStep`,
  `finPlane_le_limitRelaxed_U`, `exists_detecting_partner`: the detecting pair (`hdet`) is
  equivalent to the consumer's rank-two detection field; detection of prescribed classes at a
  compatible realized prime is not produced.
* `DegreeOneRealization.finPlane_le_U_of_signs`, `DegreeOneRealization.exists_plus_detection`:
  the conjugation `conj` and the action `T` are free parameters; they must be bound to the
  actual conjugation and the Tate action at integration, and the nonzero sign components are
  inputs.
* `exists_tameCoord_surjective`, `exists_tameCoord_surjective_at`, `innerLimit_local_surjective`:
  conditional on the local Galois group fixing the `2^i`-th roots of unity, on trivial
  coefficient action, and on chosen Frobenius and inertia elements; they are coordinate
  surjectivity helpers, not the retained local cochain comparison (inverse maps, degree zero and
  two, cup product, orientation).
* `retainedNonquadStep`: duality from the retained stage data of the fibre duality, and the
  limit diagram must be the realized one; the retained data themselves are produced elsewhere.

## Open arithmetic obligations (exact shapes in `StageInputs.lean`, `ArithLabel.lean` and
`Conjugation.lean`)

* `FrobeniusMatchesLabel` (`Conjugation.lean`; the field `frobMatch` of
  `CompatibleArithmeticLabel`): the Frobenius of the label at `q_i` is a `G_{K,S}`-conjugate of
  the restriction of `e⁻¹ Fr_i² e`. Also the field `character` (the character constraint in the
  finite quotient of the Chebotarev selection). For a continuous `α`, a finite `S`, a quadratic `K`
  and a conjugation nontrivial on `K`, both are now proved for the label built from finite-stage
  kernel elements by `compatibleArithmeticLabelFromStageKernel`
  (`ZInQKernel/Contrib/RC53Assist/StagePrimes/Arithmetic.lean`), through
  `frobeniusMatchesLabel_of_inert` and `selectedDerivativePrimes_character`
  (`ZInQKernel/Contrib/RC53Assist/FrobeniusMatch/Arithmetic.lean`).
* `ResidualCohomologyFinite` for the stage Selmer complexes: the base-change comparison
  `k ⊗ C_cont(G, M) ≅ C_cont(G, k ⊗ M)` for discrete `M`, compatible with the Selmer cone and the
  local conditions, and finiteness of the residual cohomology of the local-condition complexes.
* `LocalDegreeTwoCoordinate` and `LocalDegreeTwoNormalized` at the stage prime: the coordinate
  `H²(K_{q_i}, M_i) ≅ M_i` oriented by the tame cup product.
* The orthogonality (`OrthogonalComplementsT`) of the actual old conditions at `A_i` with
  truncated isotropy data, the input of `stageSelmerDuality`.
* The reverse maps and both homotopies of the stage duality exist on the bounded finite free
  models (a quasi-isomorphism of bounded complexes of finite free modules is a homotopy
  equivalence); they are not asserted on the unbounded cochain complexes. On those bounded models
  they are now constructed from the stage duality quasi-isomorphism (`exists_stageMatrixDiagram`,
  `ZInQKernel/Contrib/OneProof/RC/FibreDuality/StageGlobal.lean`) and assembled over all stages
  from the stagewise inputs, among them `ResidualCohomologyFinite` and a uniform bound on the
  residual ranks (`exists_retained_of_stageInputs`,
  `ZInQKernel/Contrib/OneProof/RC/FibreDuality/StageArith.lean`).
