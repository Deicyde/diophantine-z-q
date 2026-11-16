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

## Results (2026-11-15 23:13 – 23:50 PST)
- VERIFIED (compiled): `scratch/mtcm-polar/PartB.lean` — `exists_zeta` (step 2): for a CM type Φ there is ζ with ζ̄ = −ζ,
  Im φᵢ(ζ) > 0 (Mathlib `AbsoluteValue.denseRange_algebraMap_pi` at the places `mk (Φ i)`, `InfinitePlace.mk_eq_iff`).
- VERIFIED (compiled): `PartA.lean` — `latHat_decomp` (𝔞̂ = 𝔞 + 𝔟̂ for m𝔞 ⊆ 𝔟, via `exists_int_approx`) and
  `exists_approx_latHat` (E dense in 𝔸_f ⊗ E mod 𝔟̂, via `exists_den`).
- VERIFIED (compiled): `PartA3.lean` — `lattice_of_unif`: IsUniformization (cmLat Φ 𝔞) θ + UniformizationLeafAll ⇒
  N𝓞_E ⊆ 𝔞 ⊆ d⁻¹𝓞_E (comparison with the ZLattice uniformization through `analyticHomLiftC_of_leaf` both ways;
  countable-range linear maps vanish; ℝ-span count for spanning; FG for denominators).
- VERIFIED (lake build, 12231 jobs): `ZInQKernel/Contrib/OneProof/MainCMPolar.lean`; axioms of every theorem
  [propext, Classical.choice, Quot.sound] (`scratch/mtcm-polar/axioms.txt`).
  * `mainTheoremCMSign_of_polar ε : MainTheoremCMPolSign ε → CMAbVarExists → UniformizationLeafAll → GAGAMorphism →
    HcmPrinted.MainTheoremCMSign ε`
  * `mainTheoremCMArith_of_polar : MainTheoremCMPolMax → CMAbVarExists → UL → GAGA → MainTheoremCMArith`
  * `mainTheoremCM_of_pol : MainTheoremCMPol → CMAbVarExists → UL → GAGA → QMRecPrinted.MainTheoremCM`
  * `qmReciprocityL3_of_pol`, `rayClassCMAb_of_polar`, `shimuraMainCM_of_polar` (hCM).
  * converse sanity: `mainTheoremCMPolMax_of_arith`, `mainTheoremCMPol_of_mainTheoremCM` (new leaves are weaker).
- VERIFIED: `#discharges` (discharges.txt): `DISCHARGES [hCM] by MainCMPolar.shimuraMainCM_of_polar`, still assumes
  [MainTheoremCMPolMax, CMAbVarExists, WeierstrassUniformization, WeierstrassParam, WeierstrassAbVar,
  UniformizationLeafAll, GAGAMorphism], standard axioms. (`rayClassCMAb` is not a field at this base: removed by
  leaf-fold22; no current bundle field consumes MainTheoremCM.)
- VERIFIED: `FoldCheck.lean` (frozenTarget with hCM replaced by the leaves) compiles, standard axioms.
- autofold --dry-run: `autofold.json` (field hCM) and `autofold-after-split2.json` (field qmReciprocityL3) both refused
  "not a field of the current bundles" (hCM is a frozenTarget argument; qmReciprocityL3 enters only with shimura-split2's
  fold): manual fold, written in the report.
