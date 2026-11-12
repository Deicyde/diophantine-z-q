# bdr-kertheta: `ker θ` is principal for `𝓞_ℂ_p`, and Mathlib's `BDeRham` is the classical `B_dR` (Lean proofs)

Status: research note, task bdr-kertheta, 2026-11-11. Lean file `scratch/bdr-kertheta/KerTheta.lean`
(about 860 lines, `import Mathlib` only, checked with `lake env lean`: no errors, no warnings,
no `sorry`; every main theorem prints the axioms `[propext, Classical.choice, Quot.sound]` and
nothing else). Log: `scratch/bdr-kertheta/log.md`. No file under `ZInQKernel/`, `blueprint/` or
other tasks' notes was edited.

Marks: **VERIFIED** = compiled in Lean or read in a source; **STANDARD** = published, reference
given; **SPECULATIVE** = an assessment. References recalled from memory are marked UNVERIFIED.

## Verdict

**The point pkg-I4 left unchecked holds, and so does everything the task asked for: all proved in
Lean (VERIFIED).** Let `O = 𝓞_ℂ_[p]` (Mathlib's `PadicComplexInt p`), `O♭ = PreTilt O p`,
`θ = fontaineTheta O p : W(O♭) → O`.

1. **`ker θ` is principal.** `BdrKer.Cp.ker_fontaineTheta_Cp`:
   `RingHom.ker (fontaineTheta O p) = Ideal.span {xi p}`, with `xi p = (p : W(O♭)) − [p♭]`, where
   `p♭ = pFlat p` is the class of a compatible system `(p, p^{1/p}, p^{1/p²}, …)` of `p`-power
   roots of `p` in `ℂ_p`, and `untilt_pFlat : p♭♯ = p`.
2. **Mathlib's form.** `ker_fontaineThetaInvertP_Cp`: the kernel of Mathlib's
   `fontaineThetaInvertP O p` (θ with `p` inverted, the ideal along which Mathlib completes to define
   `BDeRhamPlus`) is `Ideal.span {xi' p}`, `xi'` the image of `ξ` in `W(O♭)[1/p]`. So the generator
   set that Mathlib's `BDeRham` inverts is non-empty (`isUnit_xi_BDeRham_Cp`).
3. **`B_dR = B_dR^+[1/ξ]`.** `bdREquivAway : BDeRham O p ≃ₐ[BDeRhamPlus O p] Localization.Away ξ`.
4. **`B_dR^+` is a complete DVR with uniformizer `ξ`.** `isDiscreteValuationRing_BDeRhamPlus :
   IsDiscreteValuationRing (BDeRhamPlus O p)`; `maximalIdeal_BDeRhamPlus : maximalIdeal = (ξ)`;
   `isAdicComplete_BDeRhamPlus : IsAdicComplete (ξ) (BDeRhamPlus O p)` (complete and separated
   for the `ξ`-adic = valuation topology); `isDomain_BDeRhamPlus`, `isLocalRing_BDeRhamPlus`,
   `eq_xi_pow_mul_unit` (every non-zero element is `ξⁿ·unit`).
5. **`B_dR` is a field, the fraction field of `B_dR^+`.** `isField_BDeRham : IsField (BDeRham O p)`
   and `isFractionRing_BDeRham : IsFractionRing (BDeRhamPlus O p) (BDeRham O p)` (for Mathlib's
   own structure map `BDeRhamPlus → BDeRham`). Hence `BDeRham O p` is a complete discretely valued
   field whose valuation ring is (the image of) `BDeRhamPlus O p`, which by Mathlib's definition is
   the `ker θ[1/p]`-adic completion of `W(O♭)[1/p]`. `nontrivial_BDeRham`: it is not the zero ring.
6. **Residue field `ℂ_p` (Mathlib's TODO 1).** `thetaPlusCp : BDeRhamPlus O p →+* ℂ_[p]`
   (reduction mod `ker θ[1/p]` via `AdicCompletion.evalOneₐ`, then `θ[1/p]`, then
   `awayEquivCp : 𝓞_ℂ_p[1/p] ≃ₐ[O] ℂ_[p]`), with `thetaPlusCp_surjective` and
   `ker_thetaPlusCp : ker = (ξ)`; `thetaPlus_ofPlus`: it extends `θ[1/p]`.
7. On the way: `fontaineTheta_surjective` (θ surjective for `𝓞_ℂ_p`), `isField_away_p`
   (`𝓞_ℂ_p[1/p]` is a field), `ker_fontaineThetaInvertP_isMaximal` (`(ξ')` maximal in
   `W(O♭)[1/p]`), `isDomain_away` (`W(O♭)[1/p]` is a domain), `xi'_mem_nonZeroDivisors`.

**Consequence for the de Rham leaves (pkg-I4).** pkg-I4's `BdR p` is
`Localization (DR.genMonoid p 𝓞_ℂ_[p])`, definitionally `BDeRham 𝓞_ℂ_[p] p` (pkg-I4 checks this by
`rfl`); this file's `BdR O p` is the same type. Mathlib's `BDeRhamPlus` is literally Fontaine's
definition of `B_dR^+` (the `ker θ`-adic completion of `W(O♭)[1/p]`; STANDARD: Fontaine,
*Le corps des périodes p-adiques*, Astérisque 223 (1994), §1.5? UNVERIFIED section). Items 1-5 show
that Mathlib's `BDeRham` is `B_dR^+[1/ξ]` = `Frac(B_dR^+)` with `B_dR^+` a complete DVR, which is
Fontaine's `B_dR`. So the de Rham predicate `IsDeRham` of pkg-I4 is stated over the classical
`B_dR`; the failure mode pkg-I4 flagged (empty generator set, `BDeRham = BDeRhamPlus`) is excluded.

**What remains.** Everything the task asked for is proved. Related points not done here: (a) the
compatibility of these facts with pkg-I4's Galois action `bdrAct` (e.g. `σ(ξ) = ξ·unit`, the action
is continuous) is not checked. (b) The non-vacuity facts of pkg-I4 §3.4 items 2-3
(`B_dR^{G_{ℚ_p}} = ℚ_p`, Tate's `ℂ_p(i)^{G} = 0`) need Ax–Sen–Tate and are untouched.

## 1. The Lean file

`scratch/bdr-kertheta/KerTheta.lean`. Sections:

| Part | Declarations | Content |
|---|---|---|
| A | `ker_eq_span_of_mod_p` | Complete-Nakayama criterion: `A` `p`-adically complete, `p` a non-zero-divisor on `B`, `ξ ∈ ker θ`, `ker θ ⊆ ξA + pA` ⇒ `ker θ = ξA`. Proof: iterate `x = ξy + px'` with `x' ∈ ker θ` (`p`-torsion-freeness), sum `Σ pᵏyₖ` by `IsPrecomplete`, conclude by `IsHausdorff`. |
| B | `ker_awayLift_eq_span` | `ker θ = ξA` ⇒ `ker(θ[1/p] : A[1/p] → B[1/p]) = ξ·A[1/p]`. |
| C | `ker_fontaineTheta_eq_span` | Any `p`-adically complete, `p`-torsion-free `O`, any `ϖ ∈ O♭` with `ϖ♯ = p` such that `coeff 0 c = 0 ⇒ ϖ ∣ c`: `ker θ = (p − [ϖ])`. Uses Mathlib's `mk_fontaineTheta`, `fontaineTheta_teichmuller`, `WittVector.ker_constantCoeff`. |
| C | `ker_fontaineThetaInvertP_eq_span`, `isUnit_xi_BDeRham`, `isLocalization_away_xi` | Mathlib's `fontaineThetaInvertP` kernel is `(ξ)`; `BDeRham` is a localization of `BDeRhamPlus` at the powers of `ξ` (`IsLocalization.of_le_of_exists_dvd`: each generator of `ker θ[1/p]` divides `ξ`). |
| D | `PkgI4.Cp` (copied unchanged from `scratch/pkg-I4/I4.lean`) | `𝓞_ℂ_[p]` is `p`-adically complete (instances absent from Mathlib). |
| D | `root`, `root_pow`, `root_succ_pow`, `mk_root` | `x^{(n)} := (F^{-n}x)♯`: `(x^{(n)})^{pⁿ} = x♯`, `(x^{(n+1)})^p = x^{(n)}`, `x^{(n)} mod p = coeff n x`. |
| D | `dvd_of_coeff_zero` | In `𝓞_ℂ_p♭`: `ϖ♯ = p`, `c♯ ∈ p𝓞` ⇒ `ϖ ∣ c`, via `eₙ = c^{(n)}/ϖ^{(n)} ∈ 𝓞` (norms), `e_{n+1}^p = eₙ` exactly. |
| D | `rootsOfP`, `pFlat`, `untilt_pFlat` | `p♭` from `IsAlgClosed ℂ_[p]`; `p♭♯ = p` by Hausdorffness and `dvd_sub_pow_of_dvd_sub`. |
| D | `xi`, `ker_fontaineTheta_Cp`, `xi'`, `ker_fontaineThetaInvertP_Cp`, `isUnit_xi_BDeRham_Cp`, `bdREquivAway` | Verdict 1-3. |
| D | `frobenius_surjective`, `fontaineTheta_surjective`, `isField_away_p`, `fontaineThetaInvertP_surjective`, `ker_fontaineThetaInvertP_isMaximal`, `isDomain_tilt`, `isDomain_away`, `xi_ne_zero`, `xi'_mem_nonZeroDivisors`, `ofPlus_xi'_pow_ne_zero`, `nontrivial_BDeRham` | Verdict 7; `ξ` not nilpotent in `B_dR^+` (via `evalₐ (n+1)`). |
| D | `isAdicComplete_BDeRhamPlus`, `isMaximal_span_xi`, `isLocalRing_BDeRhamPlus`, `maximalIdeal_BDeRhamPlus`, `eq_xi_pow_mul_unit`, `isDomain_BDeRhamPlus`, `isDiscreteValuationRing_BDeRhamPlus` | Verdict 4 (Mathlib's `AdicCompletion.isAdicComplete_self`, `isMaximal_map_of_le`, `isLocalRing_of_isAdicComplete_maximal`, `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`). |
| D | `isFractionRing_away_xi`, `isField_BDeRham`, `isFractionRing_BDeRham` | Verdict 5. |
| D | `thetaPlus`, `thetaPlus_ofPlus`, `thetaPlus_surjective`, `ker_thetaPlus`, `isFractionRing_away_p`, `awayEquivCp`, `thetaPlusCp`, `thetaPlusCp_surjective`, `ker_thetaPlusCp` | Verdict 6. |

`BdR O p` abbreviates `Localization (genMonoid O p)`, checked by `example : BdR O p = BDeRham O p
:= rfl` (Mathlib's `BDeRham` carries no `CommRing` instance, as pkg-I4 also found).

## 2. The mathematics (VERIFIED by the compiled proof)

Fontaine's argument (STANDARD; e.g. Brinon–Conrad, *CMI Summer School notes on p-adic Hodge
theory*, §4.4, UNVERIFIED numbering), arranged so that no valuation on `O♭` is needed:
`ker(θ mod p) = ker(O♭ → O/p) = p♭·O♭` is proved with norms on `𝓞_ℂ_p` only, through the exact
`p`-power-root sequences `x^{(n)}`, and lifted by Part A. Parts A-C hold for any `p`-adically
complete, `p`-torsion-free ring (the setting of Mathlib's θ); only Part D uses `ℂ_p` (algebraic
closedness and the norm). The DVR property: `(ξ')` is a maximal principal ideal of the domain
`W(O♭)[1/p]` (θ is surjective and `O[1/p]` is a field); its adic completion is complete for
`(ξ)`, local with maximal ideal `(ξ)`, separated, so every non-zero element is `ξⁿ·unit`, and `ξ`
is not nilpotent because `ξⁿ ∉ (ξ^{n+1})` in the domain `W(O♭)[1/p]`.

## 3. Remarks for integration

- The results apply verbatim to pkg-I4's `BdR p` (same type), and can replace pkg-I4 §3.4 item 1
  ("a reader should check") by theorems.
- Parts A-C address Mathlib's TODO 3 in `Mathlib/RingTheory/Perfectoid/BDeRham.lean` ("ker θ is
  principal when the base ring is integral perfectoid") once the divisibility hypothesis of Part C
  is derived from a perfectoid axiom; for `𝓞_ℂ_p` it is proved. TODO 2 ("`B_dR^+` is a DVR") is
  proved for `𝓞_ℂ_p` (item 4), and TODO 1 ("extend θ to `B_dR^+`") is `thetaPlus` (item 6).
