# ring-class (fleet report)

**Main result.** Two of cm-points' leaves are now theorems. Both live in
`ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean`, with axioms propext, Classical.choice and Quot.sound:
- `hprimeNormal : Package.HprimeNormal` (`H'_d/ℚ` normal);
- `iInH4 : Package.IInH4` (`i ∈ H_{n,4}`).

cm-points' TYZ-specific Shimura leaf follows from their general `CM.CMFieldOfDefinition H`, with `H`
pinned to the new `ringClassFieldD`, the ring class field of discriminant `D` built from Tau Ceti's
`ringClassField`. The link is `ringClassFieldD (−64n) = H_{n,4}` (`ringClassFieldD_tyz`). Hence
`tyzThm35ReadingA_of_cmLeaves_ringClassD` derives reading A from:
- the three 𝓛-leaves;
- `CM.CMFieldOfDefinition ringClassFieldD` (Gross 1984 / Shimura, textbook);
- `TYZSigmaFixesZn`, `Lemma318Literal HHprime`, `GenusPointLeafCM`.

The caveats stay visible: reading A is not printed in any refereed text, TYZ was read in arXiv v1 only, and
Proposition N is AI-reviewed only.

**Also proved** (new files `RingClassGalois.lean`, `RingClassTwo.lean`, `RingClassGenus.lean`):
- Bauer's theorem from Tau Ceti's Chebotarev (`le_of_splitSet_diff_subset`).
- The splitting law for subfields of ring class fields (`mem_splitSet_iff`).
- Normality over ℚ of every ring class field `ℤ+f𝓞_K` of an imaginary quadratic field and of its
  Pic-subfields (`normal_ringSubfield`, `normal_ringClassFieldBar`), and independence of the embedding
  (`ringClassFieldBar_eq_map`, `H4bar_eq_map'`, `Hprimebar_eq_map'`).
- `K_d(√−1) ⊆ H_{d,4}` (`adjI_le_H4`).
- TYZ Prop 3.2(1), `H'_d(√2) = H_{d,4}` (`Hprime_sup_sqrt_two`), via splitting in `K(√a)`
  (`mem_splitSet_adjSqrt_iff`) and Chebotarev primes in Picard classes (`exists_prime_picClass_eq`).
- Explicit genus theory `K_n(i, √p) ⊆ H_n` (`adjSqrt_le_hilbertField`), hence `L_n(i) ⊆ H'_n` and
  `ℍ'_n = ⨆ H'_{d₀}` (`HHprime_eq_iSup`).
- The Artin isomorphism `Pic(O_{d,4})/⟨σ_{1+2ϖ}⟩ ≃* Gal(H'_d/K_d)` (`artinPrime`).
- Complex conjugation inverts the Artin symbols (`conjGal_artin4`; ℚ̄ form `actsAsArtin4_conj`).
- Squares fix `i` (`fixes_iQ_of_actsAsArtin4_sq`).
- Lifts of `2Cl` with `g(n)` elements (`exists_lift_picSquares_O4`).
- The class-7 field `ringClassFieldD (−d) = H_d` (`ringClassFieldD_neg`).

Done earlier in the task (`RingClass.lean`): `H_{d,4}`, `H'_d`, `ℍ'_n`, `artin4`, genus field and `Pic[2]`
degrees, `[H_{d,4}:H'_d] = 2`, `H_d ⊆ H'_d`, and the `GenusData` bridges (`gNat_eq_gRingClass`,
`genusField_eq_fixedField_chi`).

**What compiles.** `lake build ZInQKernel.Contrib.TYZGenus.RingClassBridge` builds everything: it imports
cm-points' `Package` and x0-32's `X0`. `lake build ZInQKernel` also succeeds. There is no sorry and no
axiom, and only `ThirdParty/TauCeti/NOTICE` among existing files was changed. `diffcheck2` reports
MOD-UNNOTED 0 and NOTE-ONLY 0. The audit `scratch/ring-class/AuditBridge.lean` prints the standard three
axioms for 26 declarations.

**What remains.**
- The other cm-points leaves are CM/torsion statements, outside ring class field theory:
  `CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn`, `Lemma318Literal`, `GenusPointLeafCM`.
- TYZ's exact `Φ₀` is not recorded on this host, so cm-points' `Φ` stays existential.
- Proposal to cm-points: drop `HprimeNormal`/`IInH4` from the leaf list, and state the CM leaf as
  `CMFieldOfDefinition ringClassFieldD`.

Report: `docs/research/ring-class.md`; log: `scratch/ring-class/log.md`.
