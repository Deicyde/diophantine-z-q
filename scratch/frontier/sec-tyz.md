## 3. TYZ: `ZInQ.Literature.TYZThm35ReadingA`

Snapshot: fork main b7cdba8e; wip/tyz-cm fd418ce7 (RUNNING); wip/cm-bridge 58f42029 (active today, other host);
wip/cm-numeric bd847db7 (finished 09:41). ring-class, cm-points, x0-32 and tyz-decomp are on fork main.
Caveats that stay attached to every row (tyz-decomp §0): reading A is printed in no refereed text (only in Smith,
arXiv:1603.08479, Thm 2.1, unrefereed); TYZ was read by AI agents in arXiv v1 only (`Period7.tex` is not on this
host; line numbers `Lnnnn` are quoted from the reports named); Proposition N and the encoding were reviewed by AI
models only. TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1 = Asian J. Math. 21 (2017), no. 4, 721–774 (refereed).

### 3.1 Chain (VERIFIED: signatures read in the Lean sources at the named commits)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| A0 | `ZInQ.PropN.tyzThm35ReadingA_of_tyzInputs` | `ZInQKernel/RouteK/PropN.lean` @ main | `TYZInputs` → premise |
| A1 | `ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves` | `Contrib/TYZDecomp/Leaves.lean:380` @ main | `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`, `TYZGenusPackage` → premise |
| A2 | `ZInQ.Contrib.TYZGenus.Package.tyzThm35ReadingA_of_cmLeaves` | `Contrib/TYZGenus/Package.lean:948` @ main | h11, h1, h29, `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` |
| **A3** (finest in a Contrib module on fork main) | `ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` | `Contrib/TYZGenus/RingClassBridge.lean:55` @ main | h11, h1, h29, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` (`IInH4`, `HprimeNormal` proved there: `iInH4`, `hprimeNormal`) |
| B1 (tyz-cm, Contrib, running) | `ZInQ.Contrib.TYZGenus.Shimura.tyzThm35ReadingA_of_shimura` | `Contrib/TYZGenus/ShimuraField.lean:417` @ tyz-cm e6ac1310 | h11, h1, h29, `ShimuraReciprocityPic`, `X0.EtaModelFricke`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` |
| B2 (tyz-cm) | `Shimura.shimuraReciprocityPic_of`, `Shimura.isRatModFn_xC_of`/`_yC_of`, `xQExpRational`, `yQExpRational` (proved) | `Contrib/TYZGenus/ShimuraModFn.lean`, `ShimuraQExp.lean` @ tyz-cm da1bc29b, e124b86b | `ShimuraReciprocityModFn`, `X0.EtaModelInvariant`, `EtaCuspGrowth` → `ShimuraReciprocityPic` |
| C1 (cm-bridge, scratch only) | `ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_cmLeaves7'` | `scratch/cm-bridge/Bridge.lean:1203` @ cm-bridge 58f42029 | h11, h1, h29, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaShiftsF0`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ`, `Lemma321Five`, `TYZThm36Seven`, `BetaOnGenus7` (it splits `GenusPointLeafCM`; built on cm-numeric's `tyzThm35ReadingA_of_pinnedLeaves`, `scratch/cm-numeric/Class7.lean:570` @ bd847db7; proves `GenusFieldLeLni`, `IInHprime`, `CMFieldOfDefinition7`) |

The finest set combines C1 (for `GenusPointLeafCM`) with B1-B2 (for the CM field and `TYZSigmaFixesZn`); each
piece compiles (REPORTED by tyz-cm's and cm-bridge's logs), but **no file compiles the combination**.
`Package.lean` and `CM.lean` are identical on main, tyz-cm and cm-numeric (VERIFIED, `git diff --stat`), so the
types agree; the composition term is (agent read of both files, not compiled):
`CMBridge.tyzThm35ReadingA_of_pinnedLeaves h11 h1 h29 (Shimura.cmFieldTYZ_of_shimura hS) iInH4
(Shimura.tyzSigmaFixesZn_of hS hF) hprimeNormal h318 (cmFieldOfDefinition7_of (Shimura.cmFieldOfDefinition_of hS))
genusFieldLeLni h35 h5 (lemma321Seven_of (cmFieldOfDefinition7_of (Shimura.cmFieldOfDefinition_of hS)) h36 hb)`
with `hS := shimuraReciprocityPic_of hMF (isRatModFn_xC_of hI hG xQExpRational) (isRatModFn_yC_of hI hG yQExpRational)`.

### 3.2 Open Props of the finest set (12: 3 LEAF, 9 GLUE)

| # | Lean name | defined in | strict | citation (UNVERIFIED unless marked) | last task, newest commit | running now |
|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (weaker than printed: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz); journal theorem number UNVERIFIED | tyz-decomp (c024aaa7, on main) | no |
| T-2 | `ZInQ.Contrib.TYZDecomp.TYZLcalOne` | same | **LEAF** (a printed assertion, "Since 𝓛(1) = 1", TYZ L1082, not proved there; the value `L(E₁,1)/Ω = 1/8` is Tunnell, Invent. Math. 72 (1983)) | TYZ L1082 (read by nt-tyz); Tunnell UNVERIFIED | tyz-decomp | no |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3; report: leaf) | TYZ Lemma 2.9, L1062–1066 (journal: Lemma 2.9, per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp | no |
| T-4 | `ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn` | `Contrib/TYZGenus/ShimuraModFn.lean` @ tyz-cm da1bc29b | GLUE (stronger than any single printed statement: all `N`, every `g ∈ ℚ(X₀(N))`, all lattice pairs; report: textbook leaf) | Shimura 1971 Thm 5.4, §6.7, Thm 6.23; Silverman, *Advanced topics* II.8.2; Gross 1984 §3; Cox Cor. 11.37 | tyz-cm fd418ce7 | **yes, tyz-cm** |
| T-5 | `ZInQ.Contrib.TYZGenus.X0.EtaModelInvariant` | `Contrib/TYZGenus/X0.lean:137` @ main | GLUE (an instance of the Ligozat criterion; report: leaf) | Ligozat, Bull. SMF Mém. 43 (1975) | x0-32 (0ab05730, on main) | no |
| T-6 | `ZInQ.Contrib.TYZGenus.Shimura.EtaCuspGrowth` | `ShimuraModFn.lean` @ tyz-cm da1bc29b | GLUE (elementary from the η transformation law) | Ligozat 1975; Ono, CBMS 102, Thm 1.65 | tyz-cm fd418ce7 | **yes, tyz-cm** |
| T-7 | `ZInQ.Contrib.TYZGenus.X0.EtaModelFricke` | `Contrib/TYZGenus/X0.lean:241` @ main | GLUE (an eta-quotient identity, checked numerically) | Darmon, CBMS 101 §2 | x0-32 (on main); consumed by tyz-cm 8ca00d4d | no |
| T-8 | `ZInQ.Contrib.TYZGenus.Package.Lemma318Literal HHprime` | `Contrib/TYZGenus/Package.lean:808` @ main | **LEAF** (weaker than printed: only `⊆ A[(1+i)³]`, `n ≡ 5`; the identification of `HHprime` and of `y² = x³ + 4x` with TYZ's `ℍ'_n` and `2y² = x³ + x` is AI-reviewed) | TYZ Lemma 3.18, L2230–2232 (read by nt-tyz, cm-bridge); journal number UNVERIFIED | cm-points (on main); owner cm-numeric | no (cm-numeric idle since 09:41) |
| T-9 | `ZInQ.Contrib.TYZGenus.Package.Thm35First ℓ tyzZ` (for all `ℓ` with `IsTYZLcal ℓ`) | def `Package.lean:289` @ main; `tyzZ` in `scratch/cm-bridge/Bridge.lean:242` @ 58f42029 | GLUE (composite: Thm 3.3 ε-part, recursion, Thm 3.5 first assertion; the `z_n` translation `X_U → X₀(32)` is AI-derived, tyz-t1 §3.1; Thm 3.3's constant rests on a computation TYZ do not print, L2014–2015) | TYZ Thm 3.3 L1299–1311, L1320–1330, Thm 3.5 L1353–1356, L1295 | cm-numeric bd847db7 / cm-bridge 58f42029 | cm-bridge (other host) |
| T-10 | `ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five` | `scratch/cm-bridge/Bridge.lean:291` @ 58f42029 (copy of cm-numeric's `CMNumeric.Lemma321Five`) | GLUE (consequence of Lemma 3.21(1) through the `z_n` translation) | TYZ Lemma 3.21(1), L2496–2512, L2547–2554 | cm-bridge 58f42029 | cm-bridge |
| T-11 | `ZInQ.Contrib.TYZGenus.CMBridge.TYZThm36Seven` | `Bridge.lean:1067` @ 58f42029 | GLUE (a reading of Thm 3.6(3) with the Artin normalization converted; numerics 12/12) | TYZ Thm 3.6(3), L1424–1427; L1247–1250; L1196, L1203–1205 | cm-bridge 58f42029 | cm-bridge |
| T-12 | `ZInQ.Contrib.TYZGenus.CMBridge.BetaOnGenus7` | `Bridge.lean:1078` @ 58f42029 | GLUE (unprinted; genus characters) | TYZ L2526–2531 | cm-bridge 58f42029 | cm-bridge |

Alternatives on fork main only (finest in a kernel module, A3): T-1, T-2, T-3, T-8 and
`CM.CMFieldOfDefinition ringClassFieldD` (GLUE as stated: CM points of discriminant `D` on `A` over the ring class
field, for every `D`; Gross 1984 §3, Shimura 1971, UNVERIFIED), `Package.TYZSigmaFixesZn` (GLUE; TYZ Cor. 3.9 via
Shimura reciprocity), and the bundled `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` (GLUE). Without tyz-cm, cm-bridge's
own form replaces T-4 to T-7 by `TYZSigmaShiftsF0` (TYZ's Hecke identity L1488–1490 transported by Shimura
reciprocity; GLUE) and `CM.CMFieldOfDefinition ringClassFieldD`.

### 3.3 Findings (TYZ)
- `TYZSigmaFixesZn` has two reductions: tyz-cm's (`Shimura.tyzSigmaFixesZn_of : ShimuraReciprocityPic →
  X0.EtaModelFricke → TYZSigmaFixesZn`, Contrib, 8ca00d4d) and cm-bridge's (to `TYZSigmaShiftsF0`). tyz-cm's is finer.
- `CM.heegnerPt` is `0` when a CM value has no algebraic preimage; the CM-field leaf asserts algebraicity, so this is
  not a hole, but T-9 to T-11 are stated through the eta model `X0.phiC`, so their faithfulness also rests on
  x0-32's analytic-model statements (`X0AnalyticModel`), which are not hypotheses of the chain.
- `CMNumeric.tyzZ` and `CMBridge.tyzZ` are two constants with the same body; an integration must keep one.
- cm-numeric's report still lists `IInH4`, `HprimeNormal`, `GenusFieldLeLni` as leaves; all three are proved
  (ring-class on main; cm-bridge).
- Hecke's continuation (`ZInQ.Contrib.heckeContinuation`) is not a hypothesis anywhere in this chain; it is used
  downstream (`Literature.tyzRow5b_of_readingA`), discharged in `GZDecomp/Scope.lean`.
