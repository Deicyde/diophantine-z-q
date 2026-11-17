# cfext-proof results log

Target: `JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite`
(ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean:48), Stichtenoth 3.6.3(a) finite case.

## Plan (proof route, no new leaf)
- A := O ⊗[K] L (O = w.comap ι, a local ring); `Algebra.FormallyUnramified O A` (base change of the separable
  field extension L/K, char 0); for the prime p = φ⁻¹(m_w): localizing, Mathlib's
  `Algebra.FormallyUnramified.map_maximalIdeal` gives m_O A_p = m_{A_p}, so every a ∈ p has s·a = π·b, s ∉ p.
- every x ∈ FL is ι(c)·φ(a) (bijectivity of F ⊗ L → FL, c = coefficient of least valuation).
- Archimedean step: for d ∈ O, d ≠ 0, some π^m ∈ dO (π transcendental over K by the full-constant-field
  hypothesis; {π} transcendence basis since trdeg F/K = 1 from t; lowest coefficient of an algebraic relation
  of d over K[π]).
- iterate: x = ι(c)φ(a)/φ(s); if c ∈ m_O done; else a ∈ p, replace (c, a, s) by (cπ, b, s s').

## Results
- Step1 (`unram_step`): compiled (import Mathlib), VERIFIED. Mathlib inputs: `Algebra.FormallyUnramified.comp`,
  `EssFiniteType.comp`, `Algebra.FormallyUnramified.map_maximalIdeal` (Stacks 00UW(1)),
  `Localization.AtPrime.map_eq_maximalIdeal`, `IsLocalization.eq_iff_exists`.
- Step2 (`isAlgebraic_adjoin_of_transcendental`, `exists_pow_eq_mul`): compiled, VERIFIED. Inputs:
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`, `IsTranscendenceBasis.cardinalMk_eq_trdeg`,
  `AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite`, `IntermediateField.isAlgebraic_adjoin_iff_top`,
  `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`, `Polynomial.X_dvd_sub_C`, valuation lemmas.
- scratch/cfext-proof/CFExt.lean: verbatim copy of the def + `constantFieldExtensionUnramifiedFinite_proof`;
  `lake env lean` 7.7 s, no errors, `#print axioms`: [propext, Classical.choice, Quot.sound]. VERIFIED.
  (Step1/Step2 files merged into CFExt.lean.)
- Hypotheses actually used: CharZero only for `Algebra.IsSeparable K L` (hence `FormallyUnramified K L`); the
  function-field clause only for trdeg F/K = 1; full constant field only for "π transcendental"; of the
  bijectivity only surjectivity. Statement is TRUE as stated; no correction needed.
- Build (prebuilt tree copied from ~/dzq-check2 at d879bb73, Main.lean byte-identical):
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ConstantFieldExtensionUnramifiedFinite`
  succeeded (14274 jobs, module 38 s; only "designed for the module system" import warnings); frozenTarget axioms
  standard. VERIFIED.
- `#discharges` (scratch/cfext-proof/Discharges.lean, output discharges-output.txt):
  `DISCHARGES [OpenResearchLeaves38.constantFieldExtensionUnramifiedFinite] by
  CFExtProof.constantFieldExtensionUnramifiedFinite_proof`, `still assumes: []`, axioms standard. VERIFIED.
- `autofold.py scratch/cfext-proof/autofold.json --dry-run` (FoldDryRun.lean.txt): "strict count: 16/18 on 34 ->
  16/17 on 33; strictest 16/18 -> 16/17"; generates OpenResearchLeaves39 (= 38 without the field, no new leaf)
  and `sixContactMin_of_open56`; the output with line 1 stripped compiles (6.5 s), `sixContactMin_of_open56`
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED. Nothing written to the tree by the dry run.
