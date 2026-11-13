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
