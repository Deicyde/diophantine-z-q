# bdr-kertheta results log

- KerTheta.lean Part A `ker_eq_span_of_mod_p` (complete-Nakayama: A p-adically complete, p regular on B,
  ξ ∈ ker θ, ker θ ⊆ ξA + pA ⇒ ker θ = ξA): COMPILES (VERIFIED).
- Part B `ker_awayLift_eq_span` (ker θ = ξA ⇒ ker θ[1/p] = ξ·A[1/p]): COMPILES (VERIFIED).
- Part C `ker_fontaineTheta_eq_span` (general p-complete, p-torsion-free O; ϖ ∈ O♭ with ϖ♯ = p and
  hdiv: coeff 0 c = 0 ⇒ ϖ ∣ c ⇒ ker θ = (p − [ϖ])): COMPILES, axioms propext/choice/Quot.sound (VERIFIED).
- `ker_fontaineThetaInvertP_eq_span`, `isUnit_xi_BDeRham` (ξ in Mathlib's generator set; its image is a
  unit of BDeRham): COMPILES, standard axioms (VERIFIED).
- Part D (𝓞_ℂ_[p]; pkg-I4's `PkgI4.Cp` completeness instances copied unchanged): `pFlat` (p♭ from a
  chosen compatible system of p-power roots of p, ℂ_p alg. closed), `untilt_pFlat : p♭♯ = p`,
  `dvd_of_coeff_zero` (c♯ ∈ p𝓞 ⇒ p♭ ∣ c in 𝓞♭, via exact roots c^{(n)} = (F^{-n}c)♯ and division in ℂ_p),
  **`ker_fontaineTheta_Cp : ker θ = (p − [p♭])`**, **`ker_fontaineThetaInvertP_Cp : ker θ[1/p] = (ξ')`**,
  `isUnit_xi_BDeRham_Cp`: ALL COMPILE, axioms [propext, Classical.choice, Quot.sound] (VERIFIED, 23:37).
- `isLocalization_away_xi` (general O with ker θ = (ξ)): Mathlib's `BDeRham` is a localization of
  `BDeRhamPlus` at the powers of the single element ξ; `bdREquivAway : BDeRham 𝓞_ℂ_[p] p ≃ₐ[BDeRhamPlus]
  Localization.Away ξ` (ξ = p − [p♭]): COMPILES, standard axioms (VERIFIED).
- `frobenius_surjective`, `fontaineTheta_surjective`, `isField_away_p` (𝓞_ℂ_p[1/p] field),
  `fontaineThetaInvertP_surjective`, `ker_fontaineThetaInvertP_isMaximal` ((ξ') maximal in W[1/p]):
  COMPILE, standard axioms (VERIFIED).
- `isDomain_tilt` (from Mathlib `PreTilt.isDomain` with `(PadicComplex.valued p).v`), `isDomain_away`
  (W(𝓞_ℂ_p♭)[1/p] domain), `xi_ne_zero`, `xi'_mem_nonZeroDivisors`: COMPILE, standard axioms (VERIFIED).
- NOT PROVED: BDeRhamPlus is a DVR with uniformizer ξ; BDeRham is its fraction field / a field.
