# cm-bridge results log

## 2026-11-13

- Merged origin/wip/cm-numeric (clean). ring-class (origin/wip/ring-class) is an ancestor of HEAD (VERIFIED, git merge-base).
- `Bridge.lean` = verbatim copy of `scratch/cm-numeric/Class7.lean` (namespace CMNumeric → CMBridge, import
  RingClassBridge) + §10 rewiring:
  - `iInHprime : IInHprime` from `Lni_le_Hprimebar` + `iQ_mem_Lni`.
  - `cmFieldOfDefinition7_of : CM.CMFieldOfDefinition ringClassFieldD → CMFieldOfDefinition7` via `ringClassFieldD_neg`.
  - `tyzSigmaFixesZn_of' : TYZSigmaShiftsF0 → TYZSigmaFixesZn`.
  - `tyzThm35ReadingA_of_rewired` (hyps: 3 𝓛-leaves, CMFieldOfDefinition ringClassFieldD, TYZSigmaShiftsF0,
    Lemma318Literal HHprime, GenusFieldLeLni, Thm35First, Lemma321Five, Lemma321Seven).
- TYZ read (Period7.tex L2504–2566, Lemma `betaaction` = 3.21; L2230–2300 Lemma `torsion2`; L1408–1430 Thm `CM point2`):
  TYZ's proof of 3.21 reduces it to Thm `CM point2` (3.6) + the action of β' on L_n(i) (= σ_ϖ∘c) + Φ₀ bookkeeping.
  Lemma `torsion2` (torsion of A(ℍ'_n)) uses ramification in division fields and supersingular reduction at
  p ≡ 3 (8): not provable with current Lean infrastructure; stays a leaf (VERIFIED read).
- Plan for GenusFieldLeLni (n ≡ 7 (8)): Bauer (`le_of_splitSet_diff_subset`) with E = K_n(i, √p : p ∣ n); a prime
  𝔭 ∤ 2n split in E has −1, p squares mod 𝔭, so |O/𝔭| ≡ 1 (4) and (|O/𝔭| / p) = 1 by
  `FiniteField.isSquare_odd_prime_iff`, so every genus character χ_p([𝔭]) = 1, so [𝔭] ∈ Cl² (`picSquares_eq_iInf_ker_chi`).
- `thm36_7.py` → `thm36_7.out` (PARI 400 digits): leaf formulation of TYZ Thm 3.6(3) (L1424–1427):
  `conj(z_n) + ρ(z_n) = τ(1/2) = (2,−4)` with ρ|_{H_n} = Art([𝔭₂]^{−5}), 𝔭₂ = (2, (√−n − δ)/2) (TYZ's v₂;
  σ_{ϖ^5} geometric ⇒ arithmetic Art^{−5}), ρ(z) via Shimura reciprocity in cm-numeric's VERIFIED direction.
  Holds for all 12 squarefree n ≡ 7 (8), 7 ≤ n ≤ 103 (VERIFIED computed); wrong sign [𝔭₂]^{+5} fails in the
  8 cases where [𝔭₂]^{10} ≠ 1 (n = 23, 31, 39, 55, 71, 87, 95; and passes only where it coincides).
- `Genus.lean` (dev file, copies `genusBar`/`GenusFieldLeLni` verbatim): `genusFieldLeLni : GenusFieldLeLni`
  COMPILED, axioms [propext, Classical.choice, Quot.sound] (VERIFIED). Pieces: `picClass_maximal` (Tau Ceti's
  picClass for the maximal order = `ClassGroup.mk0`), `genusAmb n = K_n(√a : a ∈ {−1} ∪ {p ∣ n})` (Normal, finite,
  Galois), `chi_eq_one_of_isSquare` (genus characters trivial at primes split in genusAmb; Mathlib's
  `FiniteField.isSquare_odd_prime_iff`, `isSquare_neg_one_iff`), `genusField_le_genusAmb` (Bauer),
  `LniK` (L_n(i) pulled back to K_nˢ, contains K_n since √−n = ±i∏√p), `genusAmb_le_LniK`.
- `Bridge.lean` §10 (rewiring) + §11 (GenusFieldLeLni) COMPILED: `lake env lean scratch/cm-bridge/Bridge.lean`
  no errors (34 s); all audited declarations [propext, Classical.choice, Quot.sound] (VERIFIED).
  `tyzThm35ReadingA_of_cmLeaves7` hyps: TYZThm11Integral, TYZLcalOne, TYZLemma29Mod2,
  CM.CMFieldOfDefinition ringClassFieldD, TYZSigmaShiftsF0, Lemma318Literal HHprime, Thm35First, Lemma321Five,
  Lemma321Seven.
- `Bridge.lean` §12 COMPILED (0 errors): `exists_complexConj` (complex conjugation in Gal(ℚ̄/ℚ) via
  `AlgHom.fieldRange_of_normal`), `p2Ideal`/`p2Class` (TYZ's v₂ = (2, θ − (δ+1)/2)), leaf `TYZThm36Seven`,
  glue Prop `BetaOnGenus7` (unproved), `actsO_of_acts4` (restriction H_{d,4} → H_d; needed a general-K lemma
  `coe_artin_restrict` — the direct `rw [restrict_ringClassArtinEquiv] at` at K = QNeg d hit max recursion /
  kernel deterministic timeout), `actsO_conj` (complex conjugation inverts Art on H_d, from ring-class's
  `actsAsArtin4_conj`), `Z7_mem_genusBar`, `card_sqClasses`, `lemma321Seven_of : CMFieldOfDefinition7 →
  TYZThm36Seven → BetaOnGenus7 → Lemma321Seven`, `tyzThm35ReadingA_of_cmLeaves7'`. All axioms standard (VERIFIED).
- Correction to thm36_7 entry: the wrong sign fails for 7 n (23, 31, 39, 55, 71, 87, 95), not 8.
- §13 (in progress) COMPILED: `pstar`, `isSquare_pstar_iff` (QR in finite-field form with p*: IsSquare (p* : F) ↔
  IsSquare (|F| : ZMod p), from Mathlib's `quadraticChar_odd_prime`, `quadraticChar_neg_one`), `genusStar n =
  K_n(√p* : p ∣ n)`, `chi_eq_one_of_isSquare_pstar`, `genusField_le_genusStar` (Bauer). VERIFIED compiled.
- §13 COMPILED: `betaOnGenus7_of : SqrtPstarInHilbert → ArtinPstarChi → NormP2 → BetaOnGenus7`
  (equalizer field `eqField`; `IsComplexConj.apply_sqrt` γ(√D) = sgn(D)√D; `betaOneSign_pstar`;
  χ_p([𝔭₂]^{−5}) = χ_p([𝔭₂]) = legBit p 2 via `chi_mk0` + NormP2; `ZMod.exists_sq_eq_two_iff`). Remaining glue for
  BETA-7: SqrtPstarInHilbert (√p* ∈ H_n), ArtinPstarChi (Art(c)√p* = χ_p(c)√p*), NormP2 (N𝔭₂ = 2).
- `sqrtPstarInHilbert : SqrtPstarInHilbert` PROVED (VERIFIED compiled, standard axioms): `norm_sq_mod_prime3`
  (4N(β) ≡ t² mod p for n ≡ 3 (4)), `adjSqrt_pstar_le_hilbertField` (Bauer, as ring-class's
  `adjSqrt_le_hilbertField`, with `isSquare_pstar_iff`). BETA-7 now rests on ArtinPstarChi + NormP2.
- `artinPstarChi : ArtinPstarChi` PROVED (VERIFIED compiled, standard axioms): `maxSubfield S` (fixed field of
  Art(S) in H_n, finite Galois), `splitSet_kerChi_iff` (away from 2n, 𝔭 splits in the fixed field of ker χ_q
  iff q* is a square mod 𝔭, via `mem_splitSet_iff`, `picClass_maximal`, `chi_mk0`, `isSquare_pstar_iff`),
  `maxSubfield_kerChi` (= K_n(√q*), Bauer both ways), Galois correspondence (`fixingSubgroup_fixedField`,
  `le_iff_le`). BETA-7 now rests on NormP2 only.
- `normP2 : NormP2` PROVED (VERIFIED compiled): (2) = 𝔭₂𝔭̄₂ (𝔭̄₂ = (2, 1 − θ − m)), u·ū = (δ²+n)/4 even
  (`linear_combination` from 2θ = 1 + √−n, (√−n)² = −n), 𝔭₂, 𝔭̄₂ ≠ (1) (`not_two_dvd_of_im`: an element with
  imaginary part ±1/2 is not 2·𝓞), N(2) = 4.
- **`betaOnGenus7 : BetaOnGenus7` PROVED** and `lemma321Seven_of' : CMFieldOfDefinition7 → TYZThm36Seven →
  Lemma321Seven` (no glue left). All standard axioms (VERIFIED).
- Independent statement review of `TYZThm36Seven` (AI subagent, read-only, 2026-11-13): items (1) 𝔭₂ = TYZ's v₂,
  (2) σ_{ϖ^5}|_H = Art([𝔭₂])^{−5}, (3) z_n pinned correctly (depends only on δ mod 64), (4) τ(1/2) = (2,−4),
  (5) non-vacuous: OK. **PROBLEM found**: `p2Ideal` was defined from the abstract √−n, but `embed n` is an arbitrary
  ℚ-embedding, so if ιC(embed √−n) = −i√n the Lean leaf becomes the wrong-sign statement, which `thm36_7.out`
  shows false (n = 23, …). **Fixed**: `PosOrient n` (Im ιC(embed √−n) > 0) and `p2Ideal n` = (2, θ − m) if
  PosOrient else (2, 1 − θ − m) — the prime with image (2, (i√n − δ)/2) in ℂ, the one tested numerically.
  `normP2` reproved for both branches; Bridge.lean recompiled, 0 errors, all axioms standard (VERIFIED).
- `plan36.py` → `plan36.out` (VERIFIED computed, 8 n = 7…71): for TYZ's class-7 data, Q' = [32, δ, (n+δ²)/128] is a
  Heegner form with τ_{Q'} = W(τ_{Q̄}) (W τ = −1/(32τ), Q̄ = [A, −δ, 1]), its class is [𝔭₂]^5, and
  z_{Q'} = T − conj(z_n). This is the numerical backbone of the follow-up plan TYZThm36Seven ⇐ tyz-cm's
  ShimuraReciprocityPic (J = 𝔭̄₂^5 = (32, (−√−n − δ)/2), c = (−δ − i√n)/2, hand-computed lattice identity) +
  x0-32's EtaModelFricke + cm-points' cmComplexConj (proved). Not formalized (time).
  thm36_7.py refactored (main guarded for import); rerun output identical.
- **§14 COMPILED: `tyzThm36Seven_of : TyzCm.ShimuraReciprocityPic → X0.EtaModelFricke → CM.CMAlgebraic →
  TYZThm36Seven`** (VERIFIED, standard axioms). `TyzCm.ShimuraReciprocityPic` and its definitions (kappa,
  idealMeetOrder, idealLat, discOf) are a verbatim copy of tyz-cm's leaf (branch wip/tyz-cm commit 66d92d11,
  ShimuraRecip.lean; verbatim check by string containment: True); helpers kappaAlg/kappaLin/
  map_mulLeft_span_pair copied from tyz-cm's ShimuraZn.lean. Proof: J = (32, ū) = 𝔭̄₂^5 (resp. (32, u) in the
  other orientation; `span_two_pow_five`), [J] = [𝔭₂]^{−5} (`span_two_mul_span_two`, `mk0_inv_of_mul`),
  lattice identities κ(J)(L', L'_N) = ū(L, L_N) for Q' = [32, δ, (n+δ²)/128] (`latK7`, `latNK7`, and conjugates),
  Fricke τ_{Q'} = −1/(32τ_{Q̄}) (`heegnerPt_tyzForm7'`), complex conjugation (`cmComplexConj`), and the
  negative orientation handled by e = γ∘embed, ρ' = γργ⁻¹. CMAlgebraic is needed because TYZThm36Seven is not
  junk-safe (heegnerPt is 0 when no algebraic point exists).
- New final theorem `tyzThm35ReadingA_of_ringClassD_sigmaFixesZn_lemma318_thm35First_lemma321Five_shimura`
  (hyps: 3 𝓛-leaves, CMFieldOfDefinition ringClassFieldD, TYZSigmaFixesZn, Lemma318Literal, Thm35First,
  Lemma321Five, ShimuraReciprocityPic, EtaModelFricke, CMAlgebraic). VERIFIED compiled.
- Merged origin/wip/tyz-cm (0ad48a7d; their files unchanged) and built `ZInQKernel.Contrib.TYZGenus.ShimuraFricke`
  (10301 jobs, OK). tyz-cm now PROVES X0.EtaModelFricke, X0.EtaModelInvariant, X0.EtaModelEquation and reduces
  ShimuraReciprocityPic, CMValueRingClass, CMFieldOfDefinition ringClassFieldD to `Shimura.ShimuraReciprocityModFn`.
- §15 COMPILED (VERIFIED, 32 audited declarations all standard axioms): `tyzCm_shimuraReciprocityPic_eq` (rfl: the
  §14 copy is verbatim), `cmAlgebraic_of_cmValue : CMValueRingClass → CMAlgebraic`,
  `tyzThm36Seven_of_shimuraModFn : ShimuraReciprocityModFn → TYZThm36Seven`, and
  **`tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five`**: TYZ reading A from the three
  𝓛-leaves, `Shimura.ShimuraReciprocityModFn` (one textbook CM leaf), `Lemma318Literal`, `Thm35First`, `Lemma321Five`.
- Final check (2026-11-13 ~12:00 PST): `lake env lean scratch/cm-bridge/Bridge.lean` 0 errors; 32 audited declarations,
  all [propext, Classical.choice, Quot.sound] (VERIFIED). Not attempted: Lemma321Five (needs β₁-lift existence via
  Kummer theory, principal genus theorem for 𝒪_{n,4}, pinned TYZ 3.6(1)); Lemma318Literal.
