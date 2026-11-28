# gap-map-1127: what stands between `frozenTarget` and checked literature citations

Base: fork main fbe27312a (2026-11-27), 30 open hypotheses: 27 in the H bundles (`OpenResearchLeaves83`,
`OpenAddedLeaves30`; `OpenTextbookLeaves18` is empty) plus `hRC`, `hCT` and `hRank`. Strict count 9/18
(10/17 without the strictest flag). The goal (Jack, 2026-11-27): reduce every open hypothesis to checked
literature citations, that is, rows rated LEAF in `docs/one-proof/kinds.tsv`.

This is a read-only survey. Nothing was built, and no Lean was run. Two model agents read the tree and the
remote branches; every file reference below was produced by them, and the key ones were spot-checked. Claims
marked UNVERIFIED were not confirmed in a file. It replaces neither `gap-triage.md` (11-15) nor `frontier.md`
(11-16), which describe older bundles.

Tiers: **cheap** (a page read, a ruling, or a short Lean bridge whose pieces exist), **medium**, **big** (new
theory or a long manuscript argument).

Order, as the lead set it: the manuscript's own arguments first (`hRC`), then the consequence rows, then the
published rows still waiting for a reading.

## Rulings of 2026-11-27

Jack's answers, verbatim, to four questions raised by this map:

1. LEAF ratings for the Milne rows and `egaIV1757SmoothNormal`: "If you've read them and checked against the
   exact word-for-word text. Then we can rat LEAF". A row becomes LEAF only after a recorded verbatim quote
   check against the hashed copy.
2. hRank's swap to the equivalent rank-one slice of Miller Thm 4.4: "Allow equivalent swaps". A swap to a
   Lean-equivalent printed statement at the same count is allowed; a strictly stronger one is not.
3. Colmez: "Fold with Milne 7.1 (+1)".
4. hCT's swap to the Cassels 1962 form, rated LEAF: "Yes, after holder agrees".

## 1. `hRC`: the manuscript's Theorem 5.3

`ZInQ.Manuscript.RC.Wiring.RCLeaves` (`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:577`) collects
every hypothesis beyond the blueprint's `Prints`, and `restrictedConverseGenuine_of_leaves` (Leaves.lean:749)
proves Theorem 5.3 from them. It has four literature fields and three fields that hold the manuscript's
argument: `data`, `pre` (`PreLeaves`, 5 fields) and `post` (`PostLeaves`, 7 fields).

**Conclusion-shaped** below means the field's docstring says the input is equivalent, or close, to the
conclusion of the manuscript step it stands for. Discharging such a field means proving that step; rewiring
it cannot remove the step.

| field | kind | tier | next step |
|---|---|---|---|
| `data` | free choice of `WData` per (ℓ, h) | cheap to write; every discharge depends on it | fix one genuine `WData` per (ℓ, h) |
| `pre.stage_support` | definitions on the chosen data | cheap | choose S (e.g. `CompanionUnit.finalSupport`) and prove the four clauses |
| `pre.aux_factor` | definitions + manuscript sources | cheap (toy route) / big (faithful route) | faithful: `auxFactorInputs_of_realizations`, blocked on `BudgetRealization` |
| `pre.even_upper` | manuscript: (3.3a), (3.2), cubes | big | (3.2) through App E's Kato class (`Even.AppEFromKato`) |
| `pre.odd_staged` | manuscript + prints; conclusion-shaped (O.7) | big | finish `SamePlaceData` (`wip/rc-same-place1`), feed `GoodRowWire.oddStagedOfSamePlace` |
| `pre.eq35` | manuscript + glue; conclusion-shaped | big | move to the `…RG` form, then genuine outer models |
| `post.companion` | from prints + a support choice | cheap | `companionLeaf_of` with `exists_companion` |
| `post.address` | manuscript + glue; conclusion-shaped parts | big | wire `addressDensityLeaf_of_genuineEven`; KSplitSeed and density models remain |
| `post.calibration` | manuscript + prints; partly conclusion-shaped | big | rewire to `CalibrationInputsZ` or `…Lit`, then the point half |
| `post.common_coordinate` | manuscript; conclusion-shaped | medium (rewire) / big (chains) | rewire to `CommonCoordinateInputsGenuineS` |
| `post.prim_regular` | manuscript + glue; vacuity trap | big | genuine Λ-adic fibres in the `ILG` form |
| `post.clearing_model` | manuscript + glue; conclusion-shaped | big | provenance of z, λ, η for `OrigCoordLink3` |
| `post.base_zero` | manuscript + prints; conclusion-shaped | big | `HeegnerDataSqrt` and `InnerLimit45Base` at genuine data |
| `hlPrint` | print (Hoffstein–Luo) | done | none |
| `shimuraEmbeddings` | print (Shimura 1973, Thm 1) | done | none |
| `carayolEulerFactors` | glue (joint reading) | cheap rewire | `Carayol1986RationalNewformEulerFactors_of_print` |
| `faltingsRigidity` | glue (reading) | cheap rewire | `Faltings1983EulerFactorRigidityQ_of_print` |

### `PreLeaves` (Leaves.lean:235)

- **stage_support** (`StageSupport`, Wiring/StageData.lean:94). The support is a set of primes containing
  {2, 3}, the primes of ℓ and those of h_*; the prepared filter tests units on a support disjoint from the
  primes of k (tex 1974–1975, 2405–2408, 2460–2462, 8247–8258). Four definitional clauses, from which
  `PreparedSpec` and `PreDataSpec` are proved (StageData.lean:112, Leaves.lean:368). No branch work. Its weight
  is in making `data` coherent with the other fields.
- **aux_factor** (`AuxFactorInputs`, Wiring/AuxFactor3.lean:89). App G's rough-companion dictionary: even
  sources per total type, coefficient rules, unit seeds (tex 2016–2185, 2343–2401, 10055–10150).
  `auxFactor_of_inputs` is proved. The faithful route `auxFactorInputs_of_realizations`
  (AuxInputs/Assembly.lean:149) needs a `SourceFamily` from `sourceFamily_of_prints` (Waldspurger, BCDT, Hasse,
  (E.9)) and `BudgetRealization`, which is a recorded stop (rc-aux-inputs.md, rc-even-budget.md). Flags: seeds
  only at prepared types (a departure, AuxFactor3.lean:79-82). The sign-type Rédei toy `auxClauses_W₂`
  (CloudB3RC53/EvenUpper/RedeiFilter.lean:234) meets every clause, so a toy discharge looks short (UNVERIFIED).
  It would keep the form and drop the text's even sources, moving the arithmetic into even_upper.
- **even_upper** (`EvenUpperRC11Inputs`, Wiring/EvenUpper3.lean:45). The even upper bound (3.3b) (tex
  2295–2341, 10079–10129). `rc11Inputs_of_sourceFamily` (EvenUpperCubes/Application.lean:253) proves the cubes
  and (3.3a) from `SourceFamily`, `SourceRules` and (3.2). (3.2) stops at the retained Kato class
  (`Even.AppEFromKato`, Even/KatoBridge.lean:39; rc-appE-32-fixed.md). Unmerged `wip/rc-kato-p2-reroute2`
  (52476d1ac) has a conditional route; Kato 2004 at 2 keeps the gap of issue #168. Flag: the level N₀ is
  existential, and N₀ = 0 makes the families constant (EvenUpper3.lean:20-23).
- **odd_staged** (`OddStagedInstance`, StageData.lean:198). The odd objects of (3.4), the visibility models and
  the theta-side comparison (O.7) (tex 2403–2546, 8225–8405, 9101–9445). Inputs: Birch–Manin, Manin–Drinfeld
  and the twist root-number formula (glue); AEC VII.3.1 and Cornut–Jetchev (prints); the exact witness and
  detector outputs (manuscript), whose existence is proved given Serre's open image (`SerreThm3`, not in
  `Prints`). The only recent work: `SamePlaceData` on `wip/rc-same-place1` (20ec445fc, 11-27), with
  `wip/rc-model-generic6/7`; the special fibre of `point_W` is open. Conclusion-shaped: the theta side with the
  comparison is (O.7) itself (Leaves.lean:297-304).
- **eq35** (`Eq35InputsGenuineABoundedR`, Wiring/GenuineEq35R.lean:91). The uniform lower bound (3.5) (tex
  2441–2446, 4909–5202). Primitive kernel vectors, the Cramer step and (3.5) are proved from regularity, the
  (4.6) valuations and retained outer models (`eq35Target_of_inputsAR`, :151). Conclusion-shaped
  (Leaves.lean:135-157, 344-362): the configuration families are existential, the model classes are not tied
  to the instance, and finite models meet `SelmerNonquadStep`. No branch work.

### `PostLeaves` (Leaves.lean:386)

- **companion** (`CompanionLeaf`, Wiring/CompanionLeaf.lean:25). Choose k < 0 squarefree, k ≡ 1 mod 4, a unit
  square at the primes of 2N, coprime to h_*, with L_*(k) ≠ 0 (tex 2595–2603). `exists_companion`
  (CloudB3RC53/Companion/Leaf.lean:79) proves every arithmetic conjunct from Hoffstein–Luo, the BFH twist sign
  and BCDT, all supplied by `RCLeaves` and `Prints`; `companionLeaf_of` (:116) closes it given a support. The
  `CompanionUnit.Selection` route (Provider.lean:234/255) also gives `CompanionOldUnit`, which the address
  field needs. Departure: k is fixed before δ_o (CompanionLeaf.lean:21-25).
- **address** (`AddressDensityLeaf`, AddressGenuine/DensityLeaf.lean:97). The address construction at δ_o (tex
  9447–9976, 10079–10861). Chebotarev is proved. `addressDensityLeaf_of_genuineEven`
  (EvenReading/DensityLeaf.lean:68) derives FreshPrime, EvenFilter and EvenReading from a `GenuineEvenSource`.
  Still open: the odd and even density models, OddFilter, PreparedFilter, KSplitSeed (rc-ksplit-*.md).
  Conclusion-shaped: KSplitSeed is the seed lemma, EvenReading is (F.1) (Leaves.lean:119-120).
- **calibration** (`CalibrationInputsH`, Wiring/CalibrationLeaf3.lean:346). (4.6) (tex 3987–4141). Ш and
  torsion orders (manuscript, with Kolyvagin as glue), Edixhoven Thm 5.3, Milne ADT I.7.3, the moving prime and
  the Kummer model; the regulator data are proved. Three alternative interfaces exist on main and none is
  wired: `CalibrationInputsZ.toH` (KmIdentPinned.lean:546), `CalibrationInputsLit.toH`
  (CalibrationLeafLit.lean:657, nine Milne/Nekovář statements), `CalibrationInputsR.toH` (KmIdentLeaf.lean:259).
  Conclusion-shaped in its Kummer model; Branch-1 scope departure (Leaves.lean:422-426).
- **common_coordinate** (`CommonCoordinateInputsNF`, Wiring/CommonCoordinate9.lean:39). (4.7) (tex
  4142–4328). `commonCoordinateInputsNF_of_genuineS` (CommonCoordinate19Leaf.lean:113) proves it from
  `CommonCoordinateInputsGenuineS`: Milne ADT I.2.8, `IwasawaGenerators` (glue), the Cai–Chen–Liu chain inputs
  and the stage data. The rewire narrows the field without closing it. Conclusion-shaped
  (Leaves.lean:456-464).
- **prim_regular** (`PrimRegularityInputsHPK`, Wiring/GenuineSwitchHPK.lean:237). Height-one regularity of
  u_prim (tex 4976–5197). Known trap: tying the fibres to the finite-level modules makes the field vacuous
  (`regularityInputsActual_iff` forces u = 0; Leaves.lean:492-500). Variants `…ILG`, `…ILP`, `…ILA` exist; no
  branch work.
- **clearing_model** (`ClearingInputsG3Q2`, Wiring/ClearingFull.lean:80). (5.9) over the triangle (5.6) (tex
  5208–5645). Conclusion-shaped (Leaves.lean:523-531): the two-place data is discarded, any complex meets the
  family-Selmer clause, and `OrigCoordLink3` lacks the provenance the interface would need. No branch work.
- **base_zero** (`BaseZeroLeafInputsText`, Wiring/BaseZeroText.lean:174). The base-zero lemma (tex
  4330–4376). `HeegnerDataSqrt` (BCDT, Eichler–Shimura, CM theory), the two-term model, the central Selmer
  comparison, the pairing, `InnerLimit45Base`; closedness, `hlim` and Cai–Shu–Tian are proved. For torsion P
  the core is equivalent to the lemma's conclusion (Leaves.lean:562-573). No branch work.

### Literature fields

`hlPrint` (PrintsAnalytic/HoffsteinLuo.lean:63) and `shimuraEmbeddings` (NewformGlueG0/VerifiedInputs.lean:34)
are prints. `carayolEulerFactors` (GaloisCompletion.lean:858) and `faltingsRigidity` (:873) are readings;
`…_of_print` theorems (G0Prints/Carayol.lean:176, G0Prints/Faltings.lean:175) reduce them to the literal
prints plus three shared bad-prime inputs, one of them glue (`DecompositionGroupLocalGlobalGlue`). Rewiring
them is a gain only once those inputs are proved.

### Where to start on `hRC`

1. **companion**: every arithmetic conjunct is already a theorem from inputs `RCLeaves` supplies.
2. **stage_support**: definitional once `data` is fixed, and fixing `data` comes first in any discharge.
3. **aux_factor**: decide first whether a toy-route discharge is acceptable. It is formally valid but drops the
   text's sources; the faithful route waits on `BudgetRealization`.
4. **common_coordinate**: the rewire to the proved reduction narrows the field.
5. **odd_staged**: the only field with live work (`wip/rc-same-place1`); big under any ordering.

The other seven manuscript fields (even_upper, eq35, address, calibration, clearing_model, base_zero, and
prim_regular with its vacuity trap) are big, and four have no work beyond main. Seven of the twelve are
conclusion-shaped, so the bulk of Theorem 5.3 is still the manuscript's argument itself.

## 2. Consequence rows (hRank and eleven in H)

| row | why GLUE | next step | tier | who |
|---|---|---|---|---|
| hRank | rank-one slice of Miller Thm 4.4; the D2 dictionary item (Mathlib `LSeries` = Hasse–Weil L) | swap to the equivalent slice (#198), allowed by ruling 2 | cheap | integrator |
| silverbergZarhinThm34 | human reading: the Lean asserts Néron-model existence, which the print presupposes | fold `contrib/sz34-direct` (551cef5d4: model given, equivalence and existence proved), allowed by ruling 2 | cheap | integrator, then rating |
| gaudronRemondSec9LowerGR1Weak | a Lean-proved weakening of GR1 Cor. 8.4 | check whether GR1 p. 352 prints the inequality itself (UNVERIFIED); if so it is a printed sentence | cheap | reader with the hashed copy |
| afCharpolyDS965 | ruled a consequence: DS print the k = 2 charpoly without proof; transport to A_f | fold `contrib/af-ribet80-20261126` (equivalent to Ribet 1980 §4), allowed by ruling 2; Ribet's sentence cites Eichler–Shimura, so check it is not a report | medium | reader + integrator |
| colmez1992DeRhamAbVar | the print presupposes a proper model (`ProperModelExists`) | fold `contrib/colmez-proper-model-milne-20261127` (Milne Thm 7.1, count +1), per ruling 3; points (b) and (c) of the flag remain | medium | integrator |
| bergerSurveyF | Berger 2002 unread; theorem number unverified; conclusion reached through Fontaine's definitions | hashed journal copy, three lenses, fold `contrib/berger-fontaine2004-report-20261127` | medium | reader + lead |
| modularHTCoeff | Gee Fact 4.20 is a survey statement; Kato §11.3 unverified | hashed Kato (Astérisque 295) reading of (9.2.2) and §11.3 | medium | reader |
| carayolThmAFrob | weakening of DDT 3.1(a)–(d); Carayol's own form needs local Langlands in Lean | read DDT pp. 85–86 and Ribet 1977 Thm 2.3; DDT compiles others' results | medium (big for Carayol's form) | reader + Jack |
| cmHeight62 | refuted as a print 11-17; steps 0–6 proved; `Step7` open (|N(Δ)| ≤ N(J)^12 for a proper model) | prove `Step7` (CMHeight62/Assembly.lean), which removes the field | big | Lean lane |
| pazukiCor13Upper | analytic→algebraic polarization dictionary; weak uniformization; only arXiv read | uniformization on `CPts`; journal reading | big | Lean lane + reader |
| javanpeykarThm111An | Thm 1.1.1 composed with §2.3; h_Fal of a curve undefined in Lean | define h_Fal for curves and prove the §2.3 comparison, or find one print | big | Lean lane |
| deligneCanonicalModelY3EveryPrint | weakened restatement of Shimura/Deligne; locators unverified | print-shaped split on `contrib/deligne-print-shaped-20261127` (raises the count) | big | Lean lane + Jack |

## 3. Published rows waiting for a reading

| row | why GLUE | next step | tier |
|---|---|---|---|
| egaIV1757SmoothNormal | unrated; three-lens AI reading on hashed EGA scans passed | verbatim quote check, then LEAF (ruling 1) | cheap |
| milneThm125Pts | unrated; AI reading on the hashed Milne copy | verbatim quote check; decide whether its four-step derivation from Thm 12.5 is "no argument" (Lemma 12.2, p. 20, is a closer citation) | cheap |
| milneProp207At3/At5, milneTorsionCount, milneZeroPreservingHomLN | LEAF in kinds.tsv, but the recorded ruling was never given | record the verbatim check and re-attribute to ruling 1; moot if y3-milne-discharge removes the Milne rows | cheap |
| hCT | Poonen–Stoll restate Cassels without proof | rebase `fold/hct-cassels-20261126` (built on the old top `sixContactMin_of_open99`) to main, holder consent (#158), fold, rate (ruling 4) | cheap Lean, consent-blocked |
| panThm104F | arXiv v2 read; JAMS text unread | journal-text check of Thm 1.0.4 in JAMS 35 | cheap with a copy |
| buzzardLemma22Full5, buzzardXDV15Lit | read in the author's preprint; Duke text unread | Duke 87 comparison, then rate; Lemma 2.2's row also carries an orbit argument | cheap–medium |
| raynaudLNM119Normal | the p. 159 sentence reports Grothendieck ("cf. XI 1.4"), unread; LNM status needs a ruling | read XI 1.4 from a hashed copy; ruling on LNM | medium |

## Cheapest moves overall

1. Verbatim quote checks for egaIV1757SmoothNormal and milneThm125Pts (and the four Milne siblings, unless the
   discharge lands first).
2. The equivalent swaps now allowed: hRank, silverbergZarhinThm34, afCharpolyDS965.
3. The Colmez fold with Milne 7.1 (+1).
4. hCT, once the holder agrees.
5. On `hRC`: companion and stage_support, both of which first need a fixed genuine `data`.

None of these needs a new manuscript argument; `hRC`'s big fields do, and they are where the remaining work is.
