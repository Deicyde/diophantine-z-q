# rv-loc-leaves results log

## Files (each compiled alone with `lake env lean`, 2026-11-12, all new theorems [propext, Classical.choice, Quot.sound])
- T27Yu.lean: copy of scratch/pkg-I3/I3.lean + `QuatIndefinite`, `QMDichotomyYu`,
  `qmDichotomyYu_of_qmDichotomy`, `quatIndefinite_two_neg_three`, `qmDichotomy_B6`. COMPILED
  (1st run failed: missing `open scoped Quaternion`; fixed).
- PazukiR22.lean: copy of scratch/pkg-I5/I5.lean + `PazukiLiteral`, `pazuki_upper_of_literal`,
  `pazuki_logpi_of_literal`, `pazuki_plus3_of_literal`, `PazukiGoodGenus2'`,
  `PazukiGoodGenus2Literal`, `pazukiGoodGenus2_of_literal`, `pazukiGoodGenus2'_of_literal`,
  `pazukiGoodGenus2'_of_pazukiGoodGenus2`. COMPILED.
- Conventions.lean (Mathlib only): `trace_inv_fin_two`, `trace_inv_smul_fin_two` (Pan convention),
  `fibre_t_one`, `fibre_t_zero`, `fibre_points_distinct` (Elkies W-cover: index 2 at j = 0, -16/27). COMPILED.
- Placeholders.lean: repaired opaque docstrings R02, R05, R16, R17, R22 (namespace HSyn) +
  `cm_count_factor_disc_neg19`, `cm_count_factor_disc_neg4_neg3` (norm_num on jacobiSym; `decide` failed). COMPILED.

## Findings (VERIFIED = read in Lean source / compiled)
- (a) PanFor quantifies `5 ≤ p` (VERIFIED): p=3 exception never arises. Arithmetic-Frobenius trace
  form is a consequence of Pan's geometric form via tr(M⁻¹)=trM/detM (compiled), g ↦ g^ρ, ψ ↦ ψ'ε^{1-k}. FAITHFUL.
- (b) SerreTatePotentialGood, GrothendieckMonodromy, R08: `∃ K'` before `∀ σ ∀ n` (VERIFIED): one open subgroup. FAITHFUL.
- (c) faltingsHeightGood is (i/2)^g (original) normalization (VERIFIED read of hypVol). Literal Cor 1.3(2)
  ⇒ log π form ⇒ +3 form (compiled). FAITHFUL.
- (d) R02 docstring "indices 4,6,2" WRONG; QMHauptmodul states no index (VERIFIED) FAITHFUL; PR(i) e_b=(4,6,2)
  correct for Y3→P¹_j as orbifold orders + torsion-free level 3.
- (e) R05 docstring "#CM(R)=h(R)" WRONG; correct 2^b h(R), b=#{p|6 inert} (rv-h-cm §3.3 already uses it).
- (f) CarayolR17' covers all ℓ, all p≠ℓ (VERIFIED read). FAITHFUL; docstrings outdated.
- (g) CF = CuspForm (VERIFIED): R13/R14 cusp only; no consumer needs Eisenstein. FAITHFUL.
- (h) DeligneSerreFinite has `ρ.IsSemisimple` (VERIFIED). FAITHFUL.
- (i) QMDichotomy lacks "indefinite" (VERIFIED): STRONGER than Yu Thm 1.1; repaired (compiled).
- (j) R16 opaque; does not use zeta clause; docstring repaired.
