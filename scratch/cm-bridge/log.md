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
