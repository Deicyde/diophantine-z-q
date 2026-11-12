# bdr-kertheta: `ker θ` is principal for `𝓞_ℂ_p` (Lean proof)

Status: research note, task bdr-kertheta, 2026-11-11. Lean file `scratch/bdr-kertheta/KerTheta.lean`
(602 lines, checked with `lake env lean`, no `sorry`; every main theorem prints the axioms
`[propext, Classical.choice, Quot.sound]` only). Log: `scratch/bdr-kertheta/log.md`. No file under
`ZInQKernel/`, `blueprint/` or other tasks' notes was edited.

Marks: **VERIFIED** = compiled in Lean or read in a source; **STANDARD** = published, reference
given; **SPECULATIVE** = an assessment. References recalled from memory are marked UNVERIFIED.

## Verdict

**Proved in Lean (VERIFIED): the point pkg-I4 left unchecked holds.** For `O = 𝓞_ℂ_[p]` (Mathlib's
`PadicComplexInt p`):

1. `BdrKer.Cp.ker_fontaineTheta_Cp`:
   `RingHom.ker (fontaineTheta O p) = Ideal.span {xi p}`, where `xi p = (p : W(O♭)) − [p♭]` and
   `p♭ = pFlat p ∈ O♭ = PreTilt O p` is the class of a compatible system `(p, p^{1/p}, p^{1/p²}, …)`
   of `p`-power roots of `p` in `ℂ_p`, with `untilt_pFlat : p♭♯ = p`.
2. `BdrKer.Cp.ker_fontaineThetaInvertP_Cp`: the kernel of Mathlib's `fontaineThetaInvertP O p`
   (θ with `p` inverted; the ideal along which Mathlib completes to define `BDeRhamPlus`) is
   `Ideal.span {xi' p}`, `xi'` the image of `ξ` in `W(O♭)[1/p]`. So it is principal and the
   generator set inverted in `BDeRham` is non-empty (`isUnit_xi_BDeRham_Cp`).
3. `BdrKer.Cp.bdREquivAway`: `BDeRham 𝓞_ℂ_[p] p ≃ₐ[BDeRhamPlus 𝓞_ℂ_[p] p] Localization.Away ξ`.
   Mathlib's `BDeRham` (all generators of `ker θ[1/p]` inverted) **is** `B_dR^+[1/ξ]`, the classical
   construction of `B_dR` from `B_dR^+`. Had the kernel not been principal, `BDeRham` would have
   been `BDeRhamPlus` itself (empty generator set); that failure mode is now excluded.
4. Toward the DVR property: `fontaineTheta_surjective` (θ is surjective for `𝓞_ℂ_p`),
   `isField_away_p` (`𝓞_ℂ_p[1/p]` is a field), `fontaineThetaInvertP_surjective`, and
   `ker_fontaineThetaInvertP_isMaximal`: **`ker θ[1/p] = (ξ')` is a maximal ideal** of
   `W(O♭)[1/p]`, with residue field `𝓞_ℂ_p[1/p]` (which is `ℂ_p`; the identification with
   `ℂ_[p]` as a type is not stated).

**Not proved (remaining):** that `BDeRhamPlus 𝓞_ℂ_[p] p` is a discrete valuation ring with
uniformizer `ξ` and that `BDeRham` is its fraction field (hence a field, complete for the
`ξ`-adic valuation, with ring of integers `BDeRhamPlus` = the `ker θ`-adic completion). §3 lists
the exact missing steps; they are standard (Fontaine 1994, Brinon–Conrad, Prop. 4.4.6 and
Thm. 4.4.8? UNVERIFIED numbering) and need no further literature input, but they were not done
in the time available. By construction `BDeRhamPlus` *is* the `ker θ[1/p]`-adic completion of
`W(O♭)[1/p]` (Mathlib's definition), so "ring of integers = the ker θ-adic completion" reduces to
the DVR statement.

**Consequence for the de Rham leaves (pkg-I4).** pkg-I4's `IsDeRham` uses `BdR p =
BDeRham 𝓞_ℂ_[p] p`. Items 1-3 show this is `B_dR^+[1/ξ]` with `ξ = p − [p♭]` a generator of
`ker θ[1/p]`, i.e. Fontaine's `B_dR` as a ring, provided `BDeRhamPlus` is Fontaine's `B_dR^+`; the
latter is literally Mathlib's definition (`ker θ[1/p]`-adic completion of `W(O♭)[1/p]`), which is
Fontaine's definition of `B_dR^+` (STANDARD; Fontaine, *Le corps des périodes p-adiques*,
Astérisque 223 (1994), §1.5? UNVERIFIED). So the de Rham leaves state what they are meant to. The
field property of `BDeRham` is a property of the classical object, not part of its definition;
its absence in Lean does not change what `IsDeRham` means, it only means non-vacuity checks such
as `B_dR^{G} = ℚ_p` (pkg-I4 §3.4) still rest on the standard theory.

## 1. The Lean file

`scratch/bdr-kertheta/KerTheta.lean`, `import Mathlib` only. Sections:

| Part | Declarations | Content |
|---|---|---|
| A | `ker_eq_span_of_mod_p` | Complete-Nakayama criterion: `A` `p`-adically complete, `p` a non-zero-divisor on `B`, `ξ ∈ ker θ`, `ker θ ⊆ ξA + pA` ⇒ `ker θ = ξA`. Proof: iterate `x = ξ y + p x'` with `x' ∈ ker θ` (`p`-torsion-freeness), sum `Σ pᵏ yₖ` by `IsPrecomplete`, conclude by `IsHausdorff`. |
| B | `ker_awayLift_eq_span` | `ker θ = ξA` ⇒ `ker(θ[1/p] : A[1/p] → B[1/p]) = ξ·A[1/p]`. |
| C | `ker_fontaineTheta_eq_span` | For any `p`-adically complete, `p`-torsion-free `O`, any `ϖ ∈ O♭` with `ϖ♯ = p` such that `coeff 0 c = 0 ⇒ ϖ ∣ c` in `O♭`: `ker θ = (p − [ϖ])`. Uses Mathlib's `mk_fontaineTheta`, `fontaineTheta_teichmuller`, `WittVector.ker_constantCoeff` (`x − [x₀] ∈ pW` for perfect rings). |
| C | `ker_fontaineThetaInvertP_eq_span`, `isUnit_xi_BDeRham`, `isLocalization_away_xi` | Mathlib's `fontaineThetaInvertP` kernel is `(ξ)`; `BDeRham` is a localization of `BDeRhamPlus` at the powers of `ξ` (`IsLocalization.of_le_of_exists_dvd`; every generator `a` of `ker θ[1/p]` divides `ξ`). |
| D | `PkgI4.Cp` (copied unchanged from `scratch/pkg-I4/I4.lean`) | `𝓞_ℂ_[p]` is `p`-adically complete (instances absent from Mathlib). |
| D | `root`, `root_pow`, `root_succ_pow`, `mk_root` | `x^{(n)} := (F^{-n}x)♯ ∈ O`: `(x^{(n)})^{pⁿ} = x♯`, `(x^{(n+1)})^p = x^{(n)}`, `x^{(n)} mod p = coeff n x` (any `p`-complete `O`). |
| D | `dvd_of_coeff_zero` | In `𝓞_ℂ_p♭`: if `ϖ♯ = p` and `c♯ ∈ p𝓞` then `ϖ ∣ c`. Proof: `‖c^{(n)}‖^{pⁿ} = ‖c♯‖ ≤ ‖p‖ = ‖ϖ^{(n)}‖^{pⁿ}`, so `eₙ = c^{(n)}/ϖ^{(n)} ∈ 𝓞`, `e_{n+1}^p = eₙ` exactly, and `d = (eₙ mod p)` satisfies `c = ϖ d`. |
| D | `rootsOfP`, `pFlat`, `untilt_pFlat` | `p♭` from `IsAlgClosed ℂ_[p]`; `p♭♯ = p` by Hausdorffness and `dvd_sub_pow_of_dvd_sub`. |
| D | `xi`, `ker_fontaineTheta_Cp`, `xi'`, `ker_fontaineThetaInvertP_Cp`, `isUnit_xi_BDeRham_Cp`, `bdREquivAway` | The main results (Verdict 1-3). |
| D | `frobenius_surjective`, `fontaineTheta_surjective`, `isField_away_p`, `fontaineThetaInvertP_surjective`, `ker_fontaineThetaInvertP_isMaximal` | Verdict 4. |

`BdR O p` is an abbreviation for `Localization (genMonoid O p)`, checked by
`example : BdR O p = BDeRham O p := rfl` (Mathlib's `BDeRham` carries no `CommRing` instance, as
pkg-I4 also found).

## 2. The mathematics (all VERIFIED by the compiled proof)

The argument is Fontaine's (STANDARD; e.g. Brinon–Conrad, *CMI Summer School notes on p-adic Hodge
theory*, Lemma 4.4.3, UNVERIFIED numbering), organized so that no valuation on `O♭` is needed:
`ker(θ mod p) = ker(O♭ → O/p) = p♭·O♭` is shown with norms on `𝓞_ℂ_p` only, via the exact
`p`-power-root sequences `x^{(n)}`, and then lifted by Part A. Mathlib's θ is defined for any
`p`-adically complete ring, and Parts A-C are stated in that generality; only Part D uses
`ℂ_p` (algebraic closedness, the norm).

## 3. What remains for "B_dR is a complete discretely valued field with ring of integers B_dR^+"

Missing Lean steps, in order (none needs a new literature input; SPECULATIVE estimate 300-600
lines in total):

1. `W(𝓞_ℂ_p♭)[1/p]` is a domain, so `ξ'` is a non-zero-divisor. Mathlib has
   `WittVector.instIsDomain` (for perfect domains of char `p`) and `PreTilt.isDomain` (for the
   tilt of the integers of an `ℝ≥0`-valued field, here `(PadicComplex.valued p).v`), so this
   should be short; not done.
2. `ξ'ⁿ W[1/p] / ξ'^{n+1} W[1/p] ≅ W[1/p]/(ξ')`, a field by Verdict 4, using 1.
3. The `(ξ')`-adic completion of a domain along a principal maximal ideal generated by a
   non-zero-divisor with `⋂ (ξ')ⁿ`-behaviour as in 2 is a DVR with uniformizer the image of `ξ'`:
   every element not in `(ξ)` is a unit (completeness and residue field), every non-zero element
   is `ξᵏ·unit`. Mathlib's `AdicCompletion` API (`IsAdicComplete (AdicCompletion I R)`,
   `evalₐ`) covers completeness; the DVR characterization `IsDiscreteValuationRing` via
   `exists_prime`/`irreducible` would need to be assembled.
4. Then `BDeRham ≅ BDeRhamPlus[1/ξ]` (proved, `bdREquivAway`) is the fraction field of a DVR,
   hence a field (`IsFractionRing` of a DVR away from a uniformizer), complete for the
   `ξ`-adic valuation, with valuation ring `BDeRhamPlus`.
5. Not asked but related (pkg-I4 §3.4 items 2-3): `B_dR^{G_{ℚ_p}} = ℚ_p` and Tate's
   `ℂ_p(i)^{G} = 0` need Ax–Sen–Tate; untouched.

Also unproved here: Mathlib's TODO 1 (θ extended to `B_dR^+`); it follows from 3 (the residue map
of the DVR) but was not done.

## 4. Remarks for integration

- The file is self-contained and could replace pkg-I4's §3.4 item 1 by a theorem: pkg-I4's
  `BdR p` is definitionally `BdR 𝓞_ℂ_[p] p` here (both unfold to `BDeRham 𝓞_ℂ_[p] p`).
- Part A-C are general and fit Mathlib's `Mathlib/RingTheory/Perfectoid/` TODO 3 ("ker θ is
  principal when the base ring is integral perfectoid") once the divisibility hypothesis of
  Part C is derived from a perfectoid axiom; for `𝓞_ℂ_p` it is proved (Part D).
