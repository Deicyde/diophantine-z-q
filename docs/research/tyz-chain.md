# tyz-chain: the TYZ side in one importable module

Task tyz-chain, 2026-11-14. Lean: `ZInQKernel/Contrib/TYZChain/` (eight new modules). Axiom audit:
`scratch/tyz-chain/Check.lean` with output `scratch/tyz-chain/Check.out`. Log: `scratch/tyz-chain/log.md`.
Marks: **VERIFIED** (compiled, or read in a file named here), **STANDARD**, **SPECULATIVE**,
**UNVERIFIED** (theorem numbers and TYZ line numbers that were not re-read here). The TYZ source
`Period7.tex` is not on this host (`~/tyz-src` does not exist), so every TYZ line number `Lnnnn` below is
quoted from the reports of the tasks that produced the statements (tyz-decomp, tyz-35, tyz-318, cm-bridge),
not re-read.

## 0. The final hypothesis list

```lean
-- ZInQKernel/Contrib/TYZChain/Main.lean
theorem ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h2 : T318.SqrtTwoNotInHHprime)
    (h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ) :
    ZInQ.Literature.TYZThm35ReadingA
```

**VERIFIED**: `lake build ZInQKernel.Contrib.TYZChain.Main` succeeds (as do `…TYZChain.ModFn` and
`…TYZChain.SSExponent`), no `sorry`, no `axiom`; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for the main theorem and for all 80 other audited theorems
(`scratch/tyz-chain/Check.out`); `#check` prints exactly the five hypotheses below, with
`TYZThm11Integral`, `TYZLemma29Mod2`, `IsTYZLcal` from `ZInQ.Contrib.TYZDecomp`,
`ShimuraReciprocityModFn` from `ZInQ.Contrib.TYZGenus.Shimura`, `SqrtTwoNotInHHprime` from
`ZInQ.Contrib.TYZGenus.T318` and `TYZThm33Pinned` from `ZInQ.Contrib.TYZGenus.TYZ35`.

| # | hypothesis | kind | content | source of the statement | Lean definition |
|---|---|---|---|---|---|
| 1 | `TYZThm11Integral` | **LEAF** | `𝓛(m)` is an integer for odd squarefree `m ≡ 1, 3 (mod 8)` | TYZ Theorem 1.1, first assertion, odd case (L371–380, UNVERIFIED here) | `ZInQKernel/Contrib/TYZDecomp/Leaves.lean` (tyz-decomp) |
| 2 | `TYZLemma29Mod2` | **LEAF** | for every sign choice `ℓ` of `𝓛` on classes 1, 3: `Σ_{m=d₁d₂} 𝓛(d₁)𝓛(d₂) ≡ g(m) (mod 2)` (`PropN.LemmaTwoEight ℓ`) | TYZ Lemma 2.9 with Proposition 2.3, mod 2 (L1062–1066, L580–586, UNVERIFIED here) | `ZInQKernel/Contrib/TYZDecomp/Leaves.lean` (tyz-decomp) |
| 3 | `Shimura.ShimuraReciprocityModFn` | **LEAF** (textbook) | main theorem of complex multiplication for values of rational modular functions on `X₀(N)` at Heegner points, Gross's form | Shimura 1971 Thm. 5.4 with the canonical model of `X₀(N)`; Gross 1984 §3 (numbers UNVERIFIED) | `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean` (tyz-cm); reviewed by shimura-modfn |
| 4 | `T318.SqrtTwoNotInHHprime` | **GLUE** (open in general) | `∀ s ∈ ℍ'_n, s² ≠ 2` for squarefree `n ≡ 5 (mod 8)` | TYZ's Step 3 in the proof of Lemma `torsion2` (Lemma 3.18) | `ZInQKernel/Contrib/TYZChain/Lemma318.lean` (tyz-318) |
| 5 | `∀ ℓ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ` | **LEAF** | TYZ Theorem 3.3 with Lemma 3.14 (`char'`) for the pinned CM points, for every sign choice `ℓ` of `𝓛` | TYZ Theorem 3.3 (L1299–1311, proof L1865–2023) with Lemma 3.14 (UNVERIFIED here) | `ZInQKernel/Contrib/TYZChain/Thm35.lean` (tyz-35) |

So the TYZ side is now **four leaves and one glue Prop**. Three leaves are TYZ's own results (1, 2, 5),
one is the textbook main theorem of CM (3). The glue (4) is proved for every `n` whose only divisor
`≡ 5 (mod 8)` is `n` itself (`T318.sqrtTwo_not_mem_HHprime_of_single`, e.g. `n` prime), and tyz-318's
report §3.2 gives a route for the general compositum (Route A; its last steps `SigmaLift →
SqrtTwoNotInHHprime` are formalized, its first steps are not).

Notes on the leaves (from the source reports, not re-checked here):

* Leaf 5 is not literally TYZ's printed Theorem 3.3: it is stated for the pinned CM points of the fork
  and uses facts listed in the docstring of `TYZ35.TYZThm33Pinned` to pass from the printed statement
  (signs absorbed into `ε`, `z_n ∈ A(H'_n)`, independence of the choice of lifts modulo torsion; HUMAN
  CHECK there). Numerically checked by tyz-t1 (73 contributing pairs, 102 excluded characters).
* Leaf 3 was reviewed by shimura-modfn: correctly stated, a consequence of Shimura's main theorem with
  torsion plus the canonical model of `X₀(N)`, and it cannot be replaced by the `j`-form of the main
  theorem of CM (singular plane-model points occur at the Heegner points the chain uses).
* Leaves 1 and 2 are tyz-decomp's; tyz-lcal showed that the former third `𝓛`-leaf `TYZLcalOne`
  (`𝓛(1) = 1`) follows from them, so it is no longer a hypothesis.

## 1. What was consolidated

| module | source | lines | content |
|---|---|---|---|
| `TYZChain/Bridge.lean` | `scratch/cm-bridge/Bridge.lean` lines 24–3213, minus copies of tyz-cm (below) | 3146 | cm-bridge §0–§15, namespace `ZInQ.Contrib.TYZGenus.CMBridge` |
| `TYZChain/L321.lean` | `scratch/tyz-321/L321.lean` lines 3214–5477, minus a copy of `Chebotarev/FrobeniusDenseOfExists` | 2166 | tyz-321 §16a (`T321B.betaOneLiftExists`) and §16 (`T321.lemma321Five_of_shimuraModFn'`) |
| `TYZChain/Thm35.lean` | `scratch/tyz-35/Final.lean` lines 3204–3915 | 738 | tyz-35 §T (leaf `TYZThm33Pinned`), §G (`thm35First_of_lcal_thm33`), namespace `…TYZ35` |
| `TYZChain/Lemma318.lean` | `scratch/tyz-318/Lemma318.lean` | 1741 | tyz-318: `T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn` |
| `TYZChain/Lcal.lean` | `scratch/tyz-lcal/TYZLcal.lean` | 926 | tyz-lcal: `TYZLcal.tyzLcalOne_of_leaves` |
| `TYZChain/ModFn.lean` | `scratch/shimura-modfn/ModFn.lean`, minus copies of tyz-cm | 675 | shimura-modfn (not used by `Main`) |
| `TYZChain/SSExponent.lean` | `scratch/ss-exponent/SSExponent.lean`, minus a copy of tyz-318's §S | 434 | ss-exponent: `SupersingularExponentA` proved, linked to tyz-318's copy of the leaf (not used by `Main`) |
| `TYZChain/Main.lean` | new | 68 | `tyzThm35ReadingA_of_leaves` |

Total 9894 lines, against 16744 in the seven source files (the difference is the three copies of
cm-bridge's file and the copies listed below).

Import graph: `Main` ← `Thm35`, `L321`, `Lemma318`, `Lcal`; `Thm35`, `L321` ← `Bridge`; `SSExponent` ←
`Lemma318`. External imports: `TYZGenus.RingClassBridge`, `TYZGenus.ShimuraFricke` (Bridge),
`Chebotarev.FrobeniusDenseOfExists` (L321; it starts with `import Mathlib`, so `Main` imports all of
Mathlib), `TYZGenus.RingClassTwo` and Tau Ceti's `TorsionReduction` (Lemma318), `TYZDecomp.Leaves`,
`HeckeAll.Continuation`, `GaussFE.FunctionalEquation5` (Lcal), `TYZGenus.ShimuraMain` (ModFn).

**No copies between the new modules** (VERIFIED by `diff`, log entry 00:21):

* `L321.lean` lines 1–3213 are byte-identical to `Bridge.lean` lines 1–3213; the module imports
  `TYZChain.Bridge` and keeps only lines 3214–5477.
* `Final.lean` lines 1–3202 are `Bridge.lean` lines 1–3212 with `CMBridge` renamed `TYZ35` (the only other
  differences are the header); `Thm35.lean` imports `TYZChain.Bridge`, reopens `…TYZ35` with
  `open …CMBridge`, and keeps only the new sections. So `Thm35First`, `tyzZ`, `IsLiftFamily`'s
  ingredients etc. are the very constants that `Bridge` and `L321` use, and the glue in `Main` is plain
  application, no `rfl` bridging.
* The other source files imported the built Contrib modules already (`TYZGenus.RingClassBridge`,
  `TYZGenus.ShimuraFricke`, `TYZGenus.ShimuraMain`, `TYZGenus.RingClassTwo`, `TYZDecomp.Leaves`,
  `HeckeAll.Continuation`, `GaussFE.FunctionalEquation5`, Tau Ceti's `TorsionReduction`); their Props are
  either those constants or local verbatim copies checked `rfl`-equal to them inside the files
  (`T318.lemma318Literal_eq`, `ShimuraModFnTask.shimuraReciprocityModFn_eq`).

**Copies of existing Contrib declarations replaced by imports** (each VERIFIED identical by `diff` or
by the source's own `rfl` check before removal, and rebuilt afterwards):

* `L321.lean`: tyz-321's §16a contained about 130 lines copied from
  `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean` (`Zbar`, `toZbar`, `toZbar_coe`,
  `card_quot`, `FrobOn`, `FrobExistsFinite`, `FrobExistsAt`, `frobOn_anti`, `isClosed_frobOn`,
  `frobExistsAt_of_finite`, `frobExistsFinite`, the instance `IsGalois ℚ Qbar`), identical up to
  `GQ ↦ GalQ` (both are the abbreviation `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`) and docstrings.
  Now `import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists` and a selective
  `open ZInQ.Contrib.ChebFD.C10 (…)`.
* `Bridge.lean` §14: cm-bridge's verbatim copies of tyz-cm's `kappa`, `idealMeetOrder`, `idealLat`,
  `discOf`, `ShimuraReciprocityPic` (namespace `TyzCm`, checked `rfl`-equal by cm-bridge) and of the
  helpers `sqrt_mul_self_C`, `kappaRoot`, `kappaAlg`, `kappaAlg_apply`, `kappaZ`, `kappaLin`,
  `kappaLin_apply` (identical to `TYZGenus/ShimuraZn.lean` lines 41–66) are replaced by a selective
  `open ZInQ.Contrib.TYZGenus.Shimura (…)`; `TyzCm.ShimuraReciprocityPic` became
  `Shimura.ShimuraReciprocityPic` in the two statements that named it.
* `ModFn.lean` §0: the verbatim copies of `Shimura.IsRatModFn` and `Shimura.ShimuraReciprocityModFn`
  are replaced by the originals (selective `open`).
* `SSExponent.lean`: its §1–§3 (`#E(F_p) = p + 1`, `[i]`, Frobenius, `Ek`; 275 lines) were a verbatim copy
  of tyz-318's §S; it now imports `TYZChain.Lemma318` and opens `T318SS`.

**Copies kept on purpose**: the statement copies with `rfl` checks against the kernel's `Package` /
`CM` Props (cm-bridge §0 `Copy.*`, tyz-318's `T318.Lemma318Literal`). They are checks of faithfulness,
not used as substitutes (the theorems used by `Main` conclude the `Package` Props).

## 2. How `Main` assembles the chain

```
tyzThm35ReadingA_of_leaves h11 h29 hS h2 h33 :=
  T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First h11
    (TYZLcal.tyzLcalOne_of_leaves h11 h29) h29 hS
    (T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn h2)
    (TYZ35.thm35First_of_lcal_thm33 h33)
```

* `T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First` is cm-bridge's headline with
  `Lemma321Five` discharged by `T321.lemma321Five_of_shimuraModFn' hS` (tyz-321) and
  `T321B.betaOneLiftExists`.
* cm-bridge's headline in turn derives from `hS`: `CM.CMFieldOfDefinition ringClassFieldD`,
  `TYZSigmaFixesZn`, `ShimuraReciprocityPic`, `CMAlgebraic` and `TYZThm36Seven` (tyz-cm, cm-bridge
  §14–§15), and from ring-class's theorems everything else of the former cm-numeric package.

## 3. Other results now importable (not needed by `Main`)

* `T318.lemma318_at_single_unconditional`: TYZ Lemma 3.18 with no hypothesis at all for `n` whose only
  divisor `≡ 5 (mod 8)` is `n`.
* `SSExponent.supersingularExponentA`: the strong supersingular exponent (`p + 1`), which closes tyz-318's
  first route `T318.lemma318Literal_HHprime_of_ss_sqrtTwo` without a textbook leaf.
* `ShimuraModFnTask.shimuraReciprocityModFn_of_split : MainTheoremCMj → RatX0Rep →
  ShimuraReciprocityModFnSingular → ShimuraReciprocityModFn` (an alternative split of leaf 3; the
  third input is still the leaf restricted to non-isolated points, so it does not shorten the list).

## 4. Status of parallel tasks

* tyz-318, shimura-modfn, tyz-321, ss-exponent: merged (all had reports), clean merges.
* sqrt2-glue (works on hypothesis 4, `SqrtTwoNotInHHprime`): at the time of writing its branch has a
  reduction `SigmaLift ⇐ FrobNormLaw + NormSigma` and no report; not merged (SQRT2-STATUS).
* The task brief mentions cm-bridge's headline with `h5 : Lemma321Five`; that hypothesis is gone
  (tyz-321).

## 5. What remains on the TYZ side

* The four leaves 1, 2, 3, 5 (literature; to be formalized or accepted). HUMAN CHECK of leaf 5's
  passage from the printed Theorem 3.3 to the pinned form (its docstring) is still outstanding, and
  no TYZ line number was re-read in this task (the source is not on this host).
* The glue 4 (`√2 ∉ ℍ'_n` for general `n`): tyz-318 report §3.2 (Route A) and task sqrt2-glue.
* Integration: the modules are new files only; `ZInQKernel/Contrib/AllContrib.lean` was not edited (the
  rules forbid editing existing files), so `lake build ZInQKernel` does not build them until someone
  adds `import ZInQKernel.Contrib.TYZChain.Main` (and `ModFn`, `SSExponent`) there.
* No provider for `ZInQ.Contrib.tyzThm35ReadingA` can be registered from this theorem until all five
  hypotheses are theorems.
