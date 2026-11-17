# y3abu-strict log

Base 579a89bb (wip/y3abu-print); origin/main c1e4ed1b already an ancestor (merge: up to date).
Build tree: reflink copy of ~/dzq-wt/y3abu-print/.lake/build and lean/.lake/build (same HEAD 579a89bb).

## 17:35 (b) split compiles (VERIFIED)
- ZInQKernel/Contrib/OneProof/ShimuraY3Strict.lean (namespace Y3ABUStrict, imports ShimuraY3Print):
  `lake env lean` OK, no errors, no sorry.
  - ModuliLevelAtUnits Y Φ Ψ: ModuliAtUnits clause + level: ∃ w ∈ 𝒪, bEmb w = u⁻¹ + 3y (y ∈ 𝒪̂), and
    toMul (P.e.eta a) = Φu ((1/3) • ι(a*w)(τ,1)ᵀ) for all a ∈ 𝒪.
  - ModuliInterpAt = onto ∧ DCRel fibres (iff) ∧ holomorphic ∀ g ∧ ModuliLevelAtUnits.
  - ReciprocityAt = last clause of DeligneBodyAt, verbatim.
  - leaves DeligneModuliY3Every (∀ fine witness, ∃ Ψ, ModuliInterpAt), DeligneReciprocityY3Every
    (∀ fine witness, ∀ Ψ, ModuliInterpAt → ReciprocityAt).
  - glue: one_mem_OhatU, moduliAtUnits_of_level, body_of_split, deligneCanonicalModelY3Every_of_split,
    shimuraMainThmIDeligneY3AbU_of_strict (discharge from Y3FineModuliAb + the two leaves).

## 17:45 build, #discharges, autofold (VERIFIED)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraY3Strict`:
  success (14103 jobs); frozenTarget standard axioms.
- discharges.txt: `DISCHARGES [OpenResearchLeaves28.shimuraMainThmIDeligneY3AbU] by Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict
  still assumes: [Y3ABUPrint.Y3FineModuliAb, Y3ABUStrict.DeligneModuliY3Every, Y3ABUStrict.DeligneReciprocityY3Every]`,
  standard axioms; `#discharges: 45 open hypotheses, 6699 theorems checked, 15 discharge one`.
- autofold.json (3 leaves, all kind published, flags "locator UNVERIFIED: ...") --dry-run:
  strict 16/21 on 37 -> 19/20 on 39; strictest same (-1 GLUE). FoldCheck.lean compiles,
  sixContactMin_of_open39 standard axioms (foldcheck.txt).
- autofold-combined.json (with grx6ab-print, elkies-print; their argument
  (Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print ...) replaced by (Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict ...)):
  16/21 on 37 -> 22/18 on 40 (-3 GLUE). FoldCheckCombined.lean compiles, standard axioms (foldcheck-combined.txt).

## 17:50 Lemma P pieces (VERIFIED, standard axioms; axioms-lemmap.txt)
- ZInQKernel/Contrib/OneProof/ShimuraY3StrictLemmaP.lean (namespace Y3ABUStrict.LemmaP; imports Polar, QMLattice):
  - realExt, realExt_eq (E = cE₀ ⇒ E⊗ℝ = c·E0R); lemmaP_lattice_unique (∃! alternating, Rosati-†, det-1 on 𝒪, positive
    for j; j² = −1).
  - iotaR (ι over ℝ), iotaR_mul, iotaR_ofB; jτ τ explicit, jτ_sq, jτ_imJ_pos ((3+|τ|²)/(6 Im τ) > 0), iotaR_jτ,
    iotaC_jτ (ι(j_τ)(τ,1)ᵀ = i(τ,1)ᵀ), iotaC_mul_jτ (mult. by i = right mult. by j_τ).
  - lemmaP_qmTorus, lemmaP_qmTorus_eq (unique principal Riemann form of type μ on ℂ²/Λ_τ is E₀, ∀ τ ∈ ℍ).
  - eq_smul_E0K (char-0 field K: alternating †-compatible forms on B⊗K are c·E₀): level compatibility automatic.
- Not statable: Riemann forms ↔ polarizations; relative Lemma P (no polarization over a base; sir-printed §1).

## 17:58 final checks (VERIFIED)
- build Main+Discharges+ShimuraY3Strict+GRX6AbPrint+ElkiesX6StarEvery: success 14108 jobs (build-summary.txt).
- discharges.txt: DISCHARGES shimuraMainThmIDeligneY3AbU by Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict,
  still assumes [Y3FineModuliAb, DeligneModuliY3Every, DeligneReciprocityY3Every], standard axioms;
  45 open hypotheses, 6742 theorems checked, 15 discharge one.
- FoldCheck.lean, FoldCheckCombined.lean recompiled: sixContactMin_of_open39 standard axioms.

## Ratings (report §5)
- y3FineModuliAb: printed iff polarization-free print at level K3 (Boutot-Carayol III §1 / Buzzard §1; UNVERIFIED);
  from PEL print: relative Lemma P (not statable) ⇒ GLUE.
- deligneModuliY3Every: printed iff polarization-free print; from PEL print: Lemma P over ℂ (Riemann-form core proved)
  ⇒ GLUE.
- deligneReciprocityY3Every: printed (specialization; only forgetful direction, no Lemma P) in both readings.
