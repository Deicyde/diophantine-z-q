# Inventory: `ZInQ.Literature.TYZThm35ReadingA` (snapshot 2026-11-13 ~10:50 PST)

Read-only. Refs as seen locally: fork main `b7cdba8e`; `origin/wip/tyz-cm` `fd418ce7` (10:46, RUNNING);
`origin/wip/cm-bridge` `58f42029` (10:38, active today); `origin/wip/cm-numeric` `bd847db7` (finished 09:41,
"fleet summary"); ring-class `f65d2340`, cm-points `5fce4d70`, x0-32 `0ab05730`, tyz-decomp `c024aaa7`: all
ancestors of main (VERIFIED `git merge-base --is-ancestor`).
Marks: VERIFIED = read in Lean/report at the named commit; REPORTED = taken from a report, not re-checked.
No lean/lake run by me. `Period7.tex` is not on this host. cm-numeric and cm-bridge report reading it (other host).

## 1. The chain

Premise (main, `ZInQKernel/Hypotheses/CR3Literature.lean:141`, VERIFIED):
`TYZThm35ReadingA := ∀ d, d%8=5 → Squarefree d → ∀ F, IsLContinuation (shortCurve (−d²)) F → 2 ≤ analyticOrderAt F 1 → T5aCl d = 0 ∧ T5bCl d = 0`.

### 1a. Finest Contrib reduction on fork main (kernel-buildable module, not imported by `ZInQKernel.lean`)

| step | theorem (full name) | file @ commit | hypotheses |
|---|---|---|---|
| A0 | `ZInQ.PropN.tyzThm35ReadingA_of_tyzInputs` | `ZInQKernel/RouteK/PropN.lean:1488` @ main | `TYZInputs` |
| A1 | `ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves` | `Contrib/TYZDecomp/Leaves.lean:380` @ main | `h11 : TYZThm11Integral`, `h1 : TYZLcalOne`, `h29 : TYZLemma29Mod2`, `hG : TYZGenusPackage` |
| A2 | `ZInQ.Contrib.TYZGenus.Package.tyzThm35ReadingA_of_cmLeaves` | `Contrib/TYZGenus/Package.lean:948` @ main | h11 h1 h29, `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` |
| **A3 (finest on main)** | `ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` | `Contrib/TYZGenus/RingClassBridge.lean:55` @ main | h11 h1 h29, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` |

(`IInH4`, `HprimeNormal` proved as `RingClassBridge.iInH4`, `RingClassBridge.hprimeNormal` @ main, lines 28/31. VERIFIED.)

### 1b. Finer Contrib reductions on the running branch tyz-cm (Contrib modules, not on main)

| theorem | file @ commit | hypotheses → conclusion |
|---|---|---|
| `ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of` | `Contrib/TYZGenus/ShimuraZn.lean:584` @ 8ca00d4d | `ShimuraReciprocityPic`, `X0.EtaModelFricke` → `Package.TYZSigmaFixesZn` |
| `Shimura.cmFieldOfDefinition_of` | `ShimuraField.lean:340` @ e6ac1310 | `ShimuraReciprocityPic` → `CM.CMFieldOfDefinition ringClassFieldD` |
| `Shimura.tyzThm35ReadingA_of_shimura` | `ShimuraField.lean:417` @ e6ac1310 | h11 h1 h29, `ShimuraReciprocityPic`, `X0.EtaModelFricke`, `Lemma318Literal HHprime`, `∀ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` → premise (finest **single compiled Contrib theorem**) |
| `Shimura.shimuraReciprocityPic_of` | `ShimuraModFn.lean` @ da1bc29b | `ShimuraReciprocityModFn`, `IsRatModFn 32 xC`, `IsRatModFn 32 yC` → `ShimuraReciprocityPic` |
| `Shimura.isRatModFn_xC_of` / `_yC_of` | `ShimuraModFn.lean` @ da1bc29b | `X0.EtaModelInvariant`, `EtaCuspGrowth`, `XQExpRational` (resp. `YQExpRational`) |
| `Shimura.xQExpRational`, `yQExpRational` (PROVED), `cmFieldOfDefinition_of_modFn'` | `ShimuraQExp.lean` @ e124b86b | `ShimuraReciprocityModFn`, `X0.EtaModelInvariant`, `EtaCuspGrowth` → `CMFieldOfDefinition ringClassFieldD` |

All VERIFIED read in Lean source; compile + standard axioms REPORTED (`scratch/tyz-cm/log.md`).

### 1c. Finest compiled single theorem (scratch only): cm-bridge

`ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_cmLeaves7'` — `scratch/cm-bridge/Bridge.lean:1203` @ 58f42029
(scratch, `lake env lean`; NOT a Contrib module). Hypotheses (VERIFIED read):
`h11 : TYZThm11Integral`, `h1 : TYZLcalOne`, `h29 : TYZLemma29Mod2`, `hcm : CM.CMFieldOfDefinition ringClassFieldD`,
`hsh : TYZSigmaShiftsF0`, `h318 : Lemma318Literal HHprime`, `h35 : ∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ`,
`h5 : Lemma321Five`, `h36 : TYZThm36Seven`, `hb : BetaOnGenus7`.
Chain inside the file: `…_cmLeaves7'` → `…_cmLeaves7` (`genusFieldLeLni` PROVED, §11) → `…_rewired` (uses `iInH4`,
`hprimeNormal`, `iInHprime` PROVED, `cmFieldOfDefinition7_of`, `cmFieldTYZ_of_ringClassD`) → `…_pinnedLeaves`
(verbatim copy of cm-numeric `CMNumeric.tyzThm35ReadingA_of_pinnedLeaves`, `scratch/cm-numeric/Class7.lean:570` @ bd847db7)
→ `…_pinned` → `Package.tyzThm35ReadingA_of_ringClass` (main) → A1/A0. Also `lemma321Seven_of : CMFieldOfDefinition7 → TYZThm36Seven → BetaOnGenus7 → Lemma321Seven`.
Compile/axioms REPORTED (cm-bridge log: 0 errors, standard axioms).

### 1d. Finest set overall = composition 1c + 1b (each piece compiled, composition NOT compiled anywhere)

`CMBridge.tyzThm35ReadingA_of_pinnedLeaves h11 h1 h29 (Shimura.cmFieldTYZ_of_shimura hS) iInH4 (Shimura.tyzSigmaFixesZn_of hS hF) hprimeNormal h318 (cmFieldOfDefinition7_of (Shimura.cmFieldOfDefinition_of hS)) genusFieldLeLni h35 h5 (lemma321Seven_of (cmFieldOfDefinition7_of (Shimura.cmFieldOfDefinition_of hS)) h36 hb)`
with `hS := shimuraReciprocityPic_of hMF (isRatModFn_xC_of hI hG xQExpRational) (isRatModFn_yC_of hI hG yQExpRational)`.
Type-compatibility: Package.lean/CM.lean identical on main, tyz-cm and cm-numeric (VERIFIED `git diff --stat`; only
RingClass.lean differs, by additions on main). It needs one module importing both tyz-cm's Shimura* and cm-bridge's copy.
Open Props of this finest set: 12 (table §2). Alternative without tyz-cm: replace rows 4–7 by `TYZSigmaShiftsF0` + `CMFieldOfDefinition ringClassFieldD` (cm-bridge's own form).

## 2. Open Props of the finest reduction (1d)

Abbrev: T = TYZ arXiv:1411.4728v1 (Asian J. Math. 21 (2017) no. 4, 721–774, refereed). Journal locators: only Thm 3.5(2) = p. 740 and Lemma 2.9 = Lemma 2.9 come from `locators.md` (AI audit); all other journal numbers UNVERIFIED. Line numbers: read in source by the task named ("rd:"); not re-read by me.

| # | Lean name | def file @ branch/commit | report class | STRICT | citation | last task / newest commit | running now? |
|---|---|---|---|---|---|---|---|
| 1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | leaf | **LEAF** (weaker than printed: odd m only; normalization `lcalSq` transcribed second-hand, PARI ~200 values REPORTED) | T Thm 1.1 first assertion, L371–380 (rd: nt-tyz); journal number UNVERIFIED (renumbered) | tyz-decomp c024aaa7 (on main) | no |
| 2 | `TYZDecomp.TYZLcalOne` (`lcalSq 1 = 1`) | same | leaf | **LEAF** (caveat: printed *assertion* "Since 𝓛(1)=1", T L1082, not proved in T; exact value also Tunnell, Invent. Math. 72 (1983) / Cremona tables, UNVERIFIED) | T L1082 (rd: nt-tyz) | tyz-decomp | no |
| 3 | `TYZDecomp.TYZLemma29Mod2` | same | leaf | **GLUE** (mod-2 composite of Lemma 2.9 + Prop 2.3; immediate, but a composite) | T Lemma 2.9 L1062–1066 (rd: nt-tyz, lit-readingA), Prop 2.3 L580–586; repo name `LemmaTwoEight` = T's Lemma 2.9 (lit-readingA finding) | tyz-decomp | no |
| 4 | `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn` | `Contrib/TYZGenus/ShimuraModFn.lean` @ tyz-cm da1bc29b | leaf (textbook) | **GLUE**: stronger than any single printed statement (all N, every regular g ∈ ℚ(X₀(N)), all lattice pairs incl. (f,N)≠1 where L_N has larger End); combination of main theorem of CM + rational model of X₀(N) | Shimura 1971 Thm 5.4, §6.7/Thm 6.23; Silverman ATAEC II.8.2; Gross 1984 §3; Cox Cor 11.37 — all UNVERIFIED (no network) | tyz-cm fd418ce7 | **yes (tyz-cm)** |
| 5 | `ZInQ.Contrib.TYZGenus.X0.EtaModelInvariant` | `Contrib/TYZGenus/X0.lean:137` @ main | leaf (x0-32) | **GLUE** (instance of Ligozat/Gordon–Hughes–Newman criterion; conditions checked by x0-32) | Ligozat, Bull. SMF Mém. 43 (1975), UNVERIFIED locator | x0-32 0ab05730 (main); consumed by tyz-cm | no (not proved on any branch, VERIFIED git grep) |
| 6 | `Shimura.EtaCuspGrowth` | `ShimuraModFn.lean` @ tyz-cm da1bc29b | leaf (textbook) | **GLUE** (elementary from η transformation law) | Ligozat 1975; Ono CBMS 102 Thm 1.65, UNVERIFIED | tyz-cm fd418ce7 | **yes (tyz-cm)** |
| 7 | `X0.EtaModelFricke` | `X0.lean:241` @ main | leaf (x0-32) | **GLUE** (an eta identity; numerics 3 τ, 12 digits; exact Fricke forms of x, y proved in X0 §14) | W_N action: Darmon CBMS 101 §2, UNVERIFIED | x0-32 (main); consumed by tyz-cm 8ca00d4d | no |
| 8 | `ZInQ.Contrib.TYZGenus.Package.Lemma318Literal HHprime` | `Package.lean:808` @ main | leaf | **LEAF** (Lean weaker: only `⊆ A[(1+i)³]`, n≡5; caveat: Lean `HHprime`/curve `y²=x³+4x` identified with T's ℍ'_n / `2y²=x³+x` by ring-class/tyz-decomp, AI-reviewed) | T Lemma 3.18, L2230–2232 (rd: nt-tyz; cm-bridge rd L2230–2300); journal number UNVERIFIED | cm-points def; owner cm-numeric (per coordinator) | cm-numeric branch idle since 09:41 |
| 9 | `Package.Thm35First ℓ CMBridge.tyzZ` (∀ℓ, IsTYZLcal ℓ →) | def `Package.lean:289` @ main; `tyzZ` in `scratch/cm-bridge/Bridge.lean:242` @ 58f42029 (copy of cm-numeric `CMNumeric.tyzZ`) | leaf | **GLUE** (composite: Thm 3.3 ε-part + recursion + Thm 3.5 first assertion; z_n translation X_U→X₀(32) AI-derived (tyz-t1 §3.1); Thm 3.3 constant rests on unprinted computation L2014–2015) | T Thm 3.3 L1299–1311, recursion L1320–1330, Thm 3.5 L1353–1356, L1295 (rd: nt-tyz) | cm-numeric bd847db7 / cm-bridge 58f42029 | cm-bridge active (status unknown) |
| 10 | `CMBridge.Lemma321Five` (= `CMNumeric.Lemma321Five`) | `scratch/cm-bridge/Bridge.lean:291` @ 58f42029; orig `scratch/cm-numeric/Class7.lean:302` @ bd847db7 | leaf | **GLUE** (consequence of T Lemma 3.21(1) via z_n translation + pinned Φ₀ subfamily; ∃σ weaker than "any lifting"); numerics 30 cases | T Lemma 3.21(1), L2496–2512, any Φ₀ L2547–2554 (rd: rv-pn-encoding, cm-bridge) | cm-bridge 58f42029 | cm-bridge active |
| 11 | `CMBridge.TYZThm36Seven` | `Bridge.lean:1067` @ 58f42029 | leaf | **GLUE** (reading: T's geometric σ_{ϖ⁵} converted to arithmetic Art([𝔭₂])^{−5}, z_n pinned via δ; numerics 12/12, opposite sign fails 7) | T Thm 3.6(3), L1424–1427; normalization L1247–1250; z_n L1196, L1203–1205 (rd: cm-bridge, cm-numeric) | cm-bridge 58f42029 | cm-bridge active |
| 12 | `CMBridge.BetaOnGenus7` | `Bridge.lean:1078` @ 58f42029 | **glue Prop** (unproved) | **GLUE** (unprinted; looks provable: genus characters + `betaOneSign`; I checked `oddPartSqfree` is signed, so σ(√p*) = sgn(p*)(2/p)√p* matches) | T L2526–2531 + genus theory | cm-bridge 58f42029 | cm-bridge active |

Strict count: LEAF 3 (#1, #2, #8), GLUE 9.

Props closed since the earlier reports (no longer open; VERIFIED in Lean source): `IInH4`, `HprimeNormal` (ring-class, main);
`IInHprime`, `GenusFieldLeLni`, `CMFieldOfDefinition7` (from `CMFieldOfDefinition ringClassFieldD`) (cm-bridge, scratch);
`Class7GenusPtDefined` (cm-numeric glue); `XQExpRational`, `YQExpRational` (tyz-cm, e124b86b, Contrib);
`CMFieldOfDefinitionTYZ`, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn` (given rows 4–7; tyz-cm).
cm-numeric's report still lists IInH4/HprimeNormal/GenusFieldLeLni as leaves: stale.

## 3. False / vacuous / statement-change findings

None found false. Points:
1. **Ownership overlap, TYZSigmaFixesZn.** tyz-cm reduced it (8ca00d4d, Contrib, to textbook `ShimuraReciprocityPic` + `EtaModelFricke`) before its 10:25 scope change gave it to cm-numeric; cm-bridge separately reduced it to `TYZSigmaShiftsF0` (T Prop "heckeaction5"(1), L1488–1490; T's proposition number UNVERIFIED: cm-numeric gives no number, cm-bridge calls it 3.7(1)). tyz-cm's reduction is finer (ShiftsF0 = T's printed identity + Shimura reciprocity). Whoever owns it should adopt `Shimura.tyzSigmaFixesZn_of`.
2. **Junk branch of `CM.heegnerPt`** (0 if no algebraic preimage): `CMFieldOfDefinition`/`TYZSigmaFixesZn` would hold trivially if CM values weren't algebraic. Not a soundness hole: row 4 asserts algebraicity. But rows 9–11 are about `heegnerPt` via the eta model `X0.phiC`, so their *faithfulness* also depends on x0-32's `X0AnalyticModel` (Bijective/Differential/Weierstrass). Those are not hypotheses of the chain; they are an implicit faithfulness caveat.
3. **Duplicate pinned objects.** `CMNumeric.tyzZ` (cm-numeric) and `CMBridge.tyzZ` (cm-bridge) are separate constants with the same body. Row 9 must name the one the integrator keeps.
4. **Lemma321Seven (now superseded)** used "∀σ, IsBetaOneLift σ", a larger class than T's "any lifting". It was justified only through multiquadratic descent. cm-bridge replaced it by rows 11–12.
5. **Hecke and non-vacuity.** Without a continuation, `lValOne` is junk 0, and then #1 would be trivially true. Non-vacuity of the universal leaves (#3, #9) also needs #1 and #2 (`isTYZLcal_lcalChoice`) (REPORTED tyz-decomp §4.1).
6. `Package.Thm35First`/`Lemma321`/`GenusPtsDefined` take Z as a free parameter. They are closed only for a pinned Z (Package.lean §5 soundness note). In 1d, Z = pinned `tyzZ`, so this is OK.
7. Not used by the chain: T Thm 1.2 (journal 1.4) is false read literally (n = 26565, 33117; nt-tyz). Readings B/C/D are false (tyz-decomp §2).

## 4. Hecke continuation

`ZInQ.Contrib.heckeContinuation : Literature.HeckeContinuation` (`Contrib/HeckeAll/Provider.lean:10`, main, proved).
- **Upstream of the premise (inside the chain): not consumed as a Lean term.** The forward chain A0–A3, 1b, 1c never calls it (VERIFIED grep). In `Leaves.lean` it appears only in docstrings (l.32, 225, 401) and in the *converse* `genusPackage_iff_readingA` (l.407). It is used semantically: it makes `lValOne` (hence `lcalSq`, #1–#3, `IsTYZLcal`) the true L-value, with uniqueness from `IsLContinuation.eq`, and it makes "no continuation of order ≤ 1" equivalent to ord ≥ 2.
- **Downstream: consumed.** `Literature.tyzRow5b_of_readingA (hA : TYZThm35ReadingA) (hH : HeckeContinuation) : TYZRow5b` (`CR3Literature.lean:152`) picks the continuation F from hH and applies hA to it. The headline `…_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier` (`MainLiterature.lean:53`) still takes `hC : HeckeContinuation`. `Contrib/GZDecomp/Scope.lean:60` discharges it with `ZInQ.Contrib.heckeContinuation` (VERIFIED).
