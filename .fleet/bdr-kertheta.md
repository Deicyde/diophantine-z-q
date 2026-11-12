# bdr-kertheta: summary

**Main result (VERIFIED, compiled, no sorry, axioms propext / Classical.choice / Quot.sound only).**
For `O = 𝓞_ℂ_[p]`, Lean file `scratch/bdr-kertheta/KerTheta.lean` (~850 lines, `import Mathlib`,
checked with `lake env lean`, no errors or warnings) proves:

- `ker_fontaineTheta_Cp`: `ker (fontaineTheta O p) = (p − [p♭])`, with `p♭ = (p, p^{1/p}, …)` and
  `p♭♯ = p` (`untilt_pFlat`). General Parts A-C: the same for any `p`-adically complete,
  `p`-torsion-free `O` once `ϖ♯ = p` and the divisibility in `O♭` hold.
- `ker_fontaineThetaInvertP_Cp`: the kernel of Mathlib's `fontaineThetaInvertP` is principal,
  so the generator set inverted in `BDeRham` is non-empty; `bdREquivAway`: `BDeRham ≃ₐ BDeRhamPlus[1/ξ]`.
- `isDiscreteValuationRing_BDeRhamPlus`, `maximalIdeal_BDeRhamPlus = (ξ)`,
  `isAdicComplete_BDeRhamPlus` (ξ-adically complete): `B_dR^+` is a complete DVR with uniformizer ξ.
- `isField_BDeRham`, `isFractionRing_BDeRham`: `BDeRham 𝓞_ℂ_[p] p` is a field, the fraction field
  of `BDeRhamPlus` (Mathlib's structure map), so it is a complete discretely valued field whose
  valuation ring is the `ker θ`-adic completion `BDeRhamPlus`.
- `thetaPlusCp : BDeRhamPlus →+* ℂ_[p]`, surjective, kernel `(ξ)` (residue field ℂ_p; Mathlib TODO 1).

**Verdict for pkg-I4.** pkg-I4's `BdR p` is the same type (`BDeRham 𝓞_ℂ_[p] p`), so its de Rham
predicate is stated over the classical `B_dR`; the flagged failure mode (`BDeRham = BDeRhamPlus`)
cannot happen.

**Remaining (not asked, not done).** Compatibility with pkg-I4's Galois action `bdrAct`;
`B_dR^{G_{ℚ_p}} = ℚ_p` and Tate's `ℂ_p(i)^G = 0` (Ax–Sen–Tate).

Report: `docs/research/bdr-kertheta.md`; log: `scratch/bdr-kertheta/log.md`.
