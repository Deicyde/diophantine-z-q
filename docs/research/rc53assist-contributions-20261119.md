# Theorem 5.3 assist lane: contributions of 2026-11-19, with draft ledger rows

This note records the contributions of the Theorem 5.3 assist lane made on 2026-11-19, for the integrator to fold
into the logs (`docs/one-proof/credits.tsv`, `reviews.tsv`, `kinds.tsv`) in the pull request that lands each piece.
Every Lean file is new, under `ZInQKernel/Contrib/RC53Assist/`, and uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Every piece was checked by an independent AI review; the review records are kept
privately by the lane. No statement of `ZInQ.OneProof.frozenTarget` changes here; none of this removes an open row
by itself.

## Caveats (carry into the logs)

- **Jacobian import hold.** The chain `GroupDifferentials` → `S2aNumberField` → `HodgeLineBinding` →
  `HodgeLatticeIdeal` imports modules of the vendored Jacobian library (`ZInQKernel/Contrib/CloudW07JacobiansCurves/`),
  directly from `GroupDifferentials/Comparison.lean` and through the vendored `CloudB3W16Cartier/GroupDifferentials.lean`.
  The lane that owns the CM-height row reports an existing source and import hold on that family; a clean admitted
  build of this chain waits for that hold. `S2aNumberField/ProjectiveComparison.lean` also contains one lemma copied
  (not imported) from that library, `Proj.toSpecZero_appTop_res` (Apache-2.0).
- **Review isolation.** All but one of the reviews ran read-only inside the author's checkout (scratch compiles, no
  builds), not in a separate checkout with its own build directory. The Hodge-lattice review used a separate checkout.
- **Build caches.** The package build caches used were made before a local loss of the package sources on the
  build host (the sources were re-cloned at the pinned revisions); their integrity has not been re-established by a
  clean rebuild.

## Contributions

| Directory | Headline | Kind | Rests on | Commit | Review |
|---|---|---|---|---|---|
| `GroupDifferentials/` | `invariantDifferentialTrivialization : AbelianCurve.InvariantDifferentialTrivialization`; `abVar_projectiveWeierstrassModel_unconditional` | proof | nothing printed (Milne, *Abelian varieties*, IV, Prop. 6.4 quoted) | 32e200ec | approve with notes |
| `S2aNumberField/` | `abVar_projectiveWeierstrassModel_charZero`, `abVar_projectiveWeierstrassModel_numberField` | proof | nothing printed | 9c12329f | approve with notes |
| `BCDTPrint/` | `BCDTThmAPrinted` (Breuil–Conrad–Diamond–Taylor, Theorem A with condition (2)); `bcdtThmA_of_printed : BCDTThmAPrinted → PoleS12.BCDTThmA` | printed leaf + proof (trivial nebentypus) | `BCDTThmAPrinted` | b6d964b8 | print faithful; proof approve |
| `DecompositionGlue/` | `decompositionGroupLocalGlobalGlue : GlobalTrace.DecompositionGroupLocalGlobalGlue` | proof | nothing printed | 5404d2b6 | approve with notes |
| `TateCurve/` (with `LocalReadings/`) | `tateCurveTateModulePrint_of_two_prints`; `additiveReductionCoinvariantsVanish_of_semistability`; `localUnramifiedValueGroupPrint`, `localFrobeniusGenerationPrint`, `silvermanIII81GaloisWeilPairingPrint_proved` (proofs) | reduction | `SilvermanC141TateUniformizationLiteral` (Silverman, AEC, 2nd ed., Thm 14.1(a),(b), pp. 444–445, existence form as printed), `LocalSemistableTatePrint` / `GrothendieckSemistableReductionPrint` (Silverberg–Zarhin, *Reduction of abelian varieties*, arXiv:alg-geom/9602014v2, Thm 4.1, p. 4) | 9ee76703 | approve with notes |
| `DiskOrders/` (with `Limit/`, `Torsion/`) | `diskArith_address'`, `diskArith_address_sha'`; `kummerSequenceTwoPowerPrint`, `silvermanX42TwoPowerLevelPrint`, `Torsion.finite_primaryComponent` (proofs) | reduction | the nine calibration statements (Milne, *Arithmetic duality theorems*; Nekovář, *Selmer complexes*), `KummerCoefficientComparison`, the address hypotheses | e7b342d9 | approve with notes |
| `G0Prints/` | `Faltings1983EulerFactorRigidityQ_of_print`; `Carayol1986RationalNewformEulerFactors_of_print` | reduction | `Faltings1983Korollar2iiiivPrint` (Faltings 1983, §5, Korollar 2, iii ⇒ iv, p. 361), `Carayol1986CorollaireRational` (Carayol 1986, §0.8, p. 411), and the GLUE reading `Shimura1973RationalGeometricReading` | eb4d68ef | approve / approve with notes |
| `HodgeLineBinding/` | `hodgeEval_invariantDifferential` | proof (for the CM-height row) | nothing printed | 02ba363f | approve with notes |
| `HodgeLatticeIdeal/` | `invariantDifferential_ideal_dictionary` | proof (for the CM-height row) | nothing printed | eca6681a | approve with notes (separate checkout) |

Findings recorded with these pieces: the earlier form `SilvermanC141TateUniformizationPrint` asserted uniqueness
of the Tate parameter, which Theorem 14.1 does not print (the printed form is used instead); `BCDTThmAPrintedAtLevel`
is the printed statement only at the conductor and can be false for other level functions (it is not cited); the
manuscript's `silverbergzarhin` bibliography entry, Theorem 3.5, is Raynaud's criterion, not the semistable-reduction
criterion.

## Draft rows for `credits.tsv`

Columns: item, kind, contributor, ai_assisted, relayed_by, url, fold, commit (fold left for the integrator).

```tsv
RC53Assist.GroupDifferentials.invariantDifferentialTrivialization	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/32e200ec5d788e64e3816e3b056a2430194e3493		32e200ec5d788e64e3816e3b056a2430194e3493
RC53Assist.S2aNumberField.abVar_projectiveWeierstrassModel_numberField	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/9c12329f81c7ce54a015cecd2937815155b55730		9c12329f81c7ce54a015cecd2937815155b55730
RC53Assist.BCDTPrint.bcdtThmA_of_printed	reduction	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/b6d964b8f449803b293f2aae5c61a63bb4792a28		b6d964b8f449803b293f2aae5c61a63bb4792a28
RC53Assist.DecompositionGlue.decompositionGroupLocalGlobalGlue	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/5404d2b6a80a35863194abc8fc736a923a901e52		5404d2b6a80a35863194abc8fc736a923a901e52
RC53Assist.TateCurve.tateCurveTateModulePrint_of_two_prints	reduction	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/9ee767031b740890e7b617819847d4d108c9f4a7		9ee767031b740890e7b617819847d4d108c9f4a7
RC53Assist.TateCurve.LocalReadings.localUnramifiedValueGroupPrint	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/9ee767031b740890e7b617819847d4d108c9f4a7		9ee767031b740890e7b617819847d4d108c9f4a7
RC53Assist.TateCurve.LocalReadings.localFrobeniusGenerationPrint	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/9ee767031b740890e7b617819847d4d108c9f4a7		9ee767031b740890e7b617819847d4d108c9f4a7
RC53Assist.TateCurve.additiveReductionCoinvariantsVanish_of_semistability	reduction	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/7fa74e286e0563c5e4bcb0205c69086f6953e59b		7fa74e286e0563c5e4bcb0205c69086f6953e59b
RC53Assist.DiskOrders.Limit.kummerSequenceTwoPowerPrint	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/9522a2af68ba0b95573be0cd9dd1b6a1f1585b50		9522a2af68ba0b95573be0cd9dd1b6a1f1585b50
RC53Assist.DiskOrders.Torsion.finite_primaryComponent	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/e7b342d9851e8290a5cb64aae21d3f30103fbdd5		e7b342d9851e8290a5cb64aae21d3f30103fbdd5
RC53Assist.DiskOrders.diskArith_address'	reduction	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/e7b342d9851e8290a5cb64aae21d3f30103fbdd5		e7b342d9851e8290a5cb64aae21d3f30103fbdd5
RC53Assist.G0Prints.Faltings1983EulerFactorRigidityQ_of_print	reduction	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/eb4d68ef08bf23f0659a46bb371ac367baad7b77		eb4d68ef08bf23f0659a46bb371ac367baad7b77
RC53Assist.G0Prints.Carayol1986RationalNewformEulerFactors_of_print	reduction	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/eb4d68ef08bf23f0659a46bb371ac367baad7b77		eb4d68ef08bf23f0659a46bb371ac367baad7b77
RC53Assist.HodgeLineBinding.hodgeEval_invariantDifferential	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/02ba363f1352be06103b454d5db26a8ec40e2a72		02ba363f1352be06103b454d5db26a8ec40e2a72
RC53Assist.HodgeLatticeIdeal.invariantDifferential_ideal_dictionary	proof	project	yes		https://github.com/Deicyde/diophantine-z-q/commit/eca6681a6322dfed10d498155f8adbe723133d96		eca6681a6322dfed10d498155f8adbe723133d96
```

## Draft rows for `reviews.tsv` (statement checks of the new printed leaves)

Columns as in `reviews.tsv`: field, commit, reader, known_reader, edition, page, display, copy, quote, verdict,
not_read, ai_use, relayed_by, url, ruling, ruled_by, evidence. Each reading was by an AI model; no person checked it.

```tsv
BCDTThmAPrinted	b6d964b8	AI reviewer		Breuil–Conrad–Diamond–Taylor, author manuscript	1–3	Theorem A; Introduction, condition (2)	author-copy		FAITHFUL (level weakened to some N, which is allowed)		whole reading by an AI model; no person checked it			
Faltings1983Korollar2iiiivPrint	eb4d68ef	AI reviewer		Invent. Math. 73 (1983)	361	§5, Korollar 2, (iii) ⇒ (iv)	scan		FAITHFUL (specialization)		whole reading by an AI model; no person checked it			
Carayol1986CorollaireRational	eb4d68ef	AI reviewer		Ann. Sci. ENS (4) 19 (1986)	411	§0.8, Corollaire	scan		FAITHFUL (specialization, with notes)		whole reading by an AI model; no person checked it			
SilvermanC141TateUniformizationLiteral	9ee76703	AI reviewer		AEC, 2nd ed. (2009)	444–445	App. C, §14, Thm 14.1(a),(b) and the Tate equation	pdf		FAITHFUL (existence form, as printed)		whole reading by an AI model; no person checked it			
GrothendieckSemistableReductionPrint	7fa74e28	AI reviewer		arXiv:alg-geom/9602014v2	4	Theorem 4.1 (i) ⇔ (ii)	author-copy		FAITHFUL WITH NOTES (semistable = good or multiplicative)	the original SGA 7 pages	whole reading by an AI model; no person checked it			
LocalSemistableTatePrint	7fa74e28	AI reviewer		arXiv:alg-geom/9602014v2	4	Theorem 4.1 (i) ⇒ (ii)	author-copy		FAITHFUL WITH NOTES	the original SGA 7 pages	whole reading by an AI model; no person checked it			
```

## Earlier contributions of the lane (2026-11-18)

The directories of the lane's first round are either on `main` already (pull requests |116| and |117|) or carried
by |141|: among them the Frobenius-trace dictionary at good primes (proved), determinant equals degree on the Tate
module (proved), the newform-period steps G1 and G2 (proved), the weak Weil parametrization from printed results
(Shimura 1973, Faltings 1983 and the G0 statements), and the corrected coinvariant readings at bad primes, with the
false invariant readings removed and archived in `docs/research/g0-representation-route-invariants.md`.
