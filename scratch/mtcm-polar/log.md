# mtcm-polar log

## Setup (2026-11-15 22:50 PST)
- Merged origin/wip/qmrec-printed (a05c57ef) and origin/wip/hcm-printed (15055182): both clean (VERIFIED, merge commits de8041d2c, d9ad1f877).
- Target: `HcmPrinted.MainTheoremCMArith` (= `MainTheoremCMSign 1`, ShimuraMainCMPrinted.lean) and hence
  `QMRecPrinted.MainTheoremCM` (via `mainTheoremCM_of_arith`).

## Plan (statements)
- LEAF `MainTheoremCMPolMax`: MainTheoremCMSign 1 restricted to `𝔞` an `𝓞_E`-stable lattice in `E` with a
  Riemann-form datum `ζ` (`conj ζ = -ζ`, `Im φᵢ(ζ) > 0`, `Tr(ζ x ȳ) ∈ ℤ` on `𝔞`): Shimura's polarized
  `(A, C, θ)` of type `(E, Φ; 𝔞, ζ)` with maximal-order lattice.
- LEAF `CMAbVarExists`: Shimura's converse (existence of `(A, C, θ)` of type `(E, Φ; 𝔟, ζ)`), stated as
  existence of `B : AbVar ℂ`, `dim B = g`, with a uniformization by `Φ(𝔟)`, for `𝔟` an `𝓞_E`-stable lattice + ζ.
- Glue (Lean): (2) ζ exists in `𝓞_E` for any CM type; (3) `𝔟₀ = N·𝓞_E ⊆ 𝔞 ⊆ d⁻¹𝓞_E`, isogeny `μ : B₀ → A`
  (HomLatticeCorr), `μ^σ` by the pullback property + rigidity, `θ' = μ^σ ∘ θ'_{B₀}`.
- Existing infrastructure found (VERIFIED by reading): `analyticHomLiftC_of_leaf` (TailQ.lean:620, lift without
  dimension hypothesis), `exists_isUniformization_of_leaf` (UnifBridge.lean:80), `bcC/projC/ptE` (TailQ.lean:1009),
  `MulRigidity.isMonHom_of_geometricallyIntegral` (FrobChain/Rigidity.lean:170), `exists_den`,
  `exists_int_approx` (RayClassShimura.lean:2656/2728), `QMRecPrinted.pt_ext` (QMRecPrinted.lean:706).
