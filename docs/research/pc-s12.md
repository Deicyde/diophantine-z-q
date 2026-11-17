# pc-s12: round 2 of fork issue #83 (Theorem 5.2 from Theorem 5.3), with Elliot's supplement S12

Task pc-s12, 2026-11-17, worktree `wip/pc-from-rc` (round 1: `docs/research/pc-from-rc.md`).
Sources: `diophantine_zq.tex` Section 5 (tex L1019–1121), and Elliot's supplement **S12**
(`research/version14/retained-sources/parity-frozen-4eaee875.tex` at upstream main 970ec6bf3, md5
5b8d6f645f240603135c536001dd4756; a local untracked copy, not committed). Every use of S12 is
labelled ELLIOT (supplement) with its line numbers.

## Main result

**Proved in Lean** (no `sorry`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`;
`scratch/pc-s12/axioms-output.txt`), in `ZInQKernel/Contrib/OneProof/PoleCompletenessFromRCGenuine.lean`:

```
ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine
    (hRC : SelmerTwoPower.RestrictedConverseGenuine)  -- Theorem 5.3 as printed (P := SelmerCorankOne)
    (h54 : Lemma54)        -- Lemma 5.4 over Tau Ceti's Sel₂ and Sel_{2^∞} (cited leaf, Poonen–Stoll)
    (hKum : KummerSelmerM) -- #Sel₂(E_ℓ/ℚ) = #SelM ℓ (textbook GLUE: Silverman X.1.4)
    (hB : BCDTThmA)        -- modularity (printed leaf)
    (hK : KolyvaginThm1)   -- r = 1: rank one and finite Ш (printed leaf, preprint)
    (hMW : MordellWeil) :  -- Mordell (textbook leaf)
  Manuscript.PoleCompleteness                          -- Theorem 5.2
```

This is the Done-when of #83 with every GLUE statement of round 1 now proved except the Kummer
identification `KummerSelmerM`:

| round-1 hypothesis | status now |
| --- | --- |
| `MatrixRealization` | **proved** (`PoleS12.matrixRealization`), from S12 `par:simultaneous-matrices` |
| `LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood` | **no longer needed**: the dimension-three count is proved (`PoleS12.dimThreeCount`) from S12 `par:descent`, with every local condition in Lean |
| `DimThreeCount`, `SimultaneousConstruction` | **proved** (`PoleS12.dimThreeCount`, `PoleS12.simultaneousConstruction`) |
| `Lemma54At P` | at `P := SelmerCorankOne`: from `Lemma54` + `KummerSelmerM` (`lemma54At_of_printed`) |
| `KolyvaginRankOne` | from `BCDTThmA` + `KolyvaginThm1` (`kolyvaginRankOne_of_printed`) |
| `MordellWeil` | unchanged (textbook leaf) |

The abstract-`P` development is kept: `poleCompleteness_of_restrictedConverse_abstract P :
RestrictedConverse P → Lemma54At P → KolyvaginRankOne → MordellWeil → PoleCompleteness`.

**Non-vacuity (correction (e)), proved:** `selM_support`/`selM_finite`: if `p ∤ 6ℓ` then `p`
divides neither coordinate of a class of `SelM ℓ`, so `SelM ℓ` is finite and `ncard = 8` is a
genuine count.

**Manuscript verdict:** no error found in tex L1019–1121 or in S12's `par:descent` and
`par:simultaneous-matrices`. Every gap noted in round 1 is filled by S12, and the filled argument
now compiles. S11 is not needed (see Known issues).

## Manuscript check

One row per step of tex L1019–1121 that this route formalizes or relies on. Verdicts:
**OK** (the text is right as written), **gap filled** (right, but an argument is omitted; S12 or
this task supplies it), **error**, **unverified** (not checked against its source).
"Lean" names the theorem that now checks the step.

| # | tex lines (S12 lines) | step | verdict | reason |
| --- | --- | --- | --- | --- |
| 1 | L1020–1024 | divisors of 2730 realize all real/2-adic/3-adic signatures; `5,7,13` give a basis | OK | Lean: `bookkeeping` (round 1) |
| 2 | L1024–1032 | `β ≡ 17`, `θ ≡ 1 (mod 24)`, disjoint supports, mutual local squares | OK | Lean: `bookkeeping`; matches S12 `par:cross-squares` (S12 L172–178) |
| 3 | L1033–1035 | simultaneous construction "in S11–S12" | gap filled | S11 is not available under that name; S12's `par:descent` (S12 L300–454) and `par:simultaneous-matrices` (S12 L543–683) give the whole construction, so S11 is not needed. Lean: `simultaneousConstruction` |
| 4 | L1036–1040 (S12 L267–279, L301–315) | `s_i`, `λ_i`, `K`, target `ker K = ⟨1, 1_β⟩`, `λ ∉ im K` | OK | identical to S12 (`par:matrices`, `par:matrix-target`); Lean: `MatrixConditions` (round 1) |
| 5 | L1041–1043 (S12 L567–571) | `d−1` slots of type `(0,0)`, one `q₀` of type `(1,1)`, by residues `1`, `7 (mod 12)` | OK | Lean: `exists_aux_primes`, `lsym_three_of_one`, the `q₀ ≡ 7` choice in `matrixRealization` |
| 6 | L1044 (S12 L606–610) | cross-block columns `e_i + e_d` | OK | a basis of the even-sum hyperplane of `𝔽₂^B`, as S12 requires; Lean: `block_injOn` (columns `e_b + e_{b*}`) |
| 7 | L1045–1048 (S12 L581–604) | rank-one correction `K♯ = K + λaᵗ` | gap filled | tex leaves `a` undefined; S12 L581–583: `a = e_{q₀} + e_{b*}` (`aᵗ1 = 0`, `aᵗ1_B = 1`); `K = K♯T` gives both targets from `ker K♯ = ⟨1⟩`. Lean: `sharp_targets` |
| 8 | L1046–1052 (S12 L606–652) | deleting `q₀` leaves `[[A, C],[Cᵗ, 0]]`, `1ᵗA1 = 1`, nonsingular | OK | the nonsingularity argument is complete; tex's `D₁` is not diagonal (S12 L641: "no symmetry of A is required"). Lean: `sharp_ker_of_deleted`, `block_injOn` |
| 9 | L1052–1053 (S12 L654–658) | adding the support of `θ` preserves the block | gap filled | needs the cross row sums `Σ_J [q_j/q_i] = 0` (mutual local squares, S12 L561–565) and `I–J` symbols `0`. Lean: `hblockJ` in `matrixRealization` |
| 10 | L1053–1056 (S12 L658–666) | free `q₀`-symbols toggle the new diagonal; full-product coefficient one; one assignment serves both supports | gap filled | correct because only one determinant varies: the `q₀–J` bits do not enter the smaller matrix (S12 L666; correction (d)). Over `𝔽₂`, "leading coefficient one" for two varying determinants would not suffice (`f = x`, `g = x + 1`). Lean: `exists_toggle_injOn` (toggles supported on `J`; the smaller support uses `d = 0` off `J`) |
| 11 | L1057–1058 (S12 L668–679) | reciprocity, CRT, Dirichlet realize the symbols by distinct primes | OK | Lean: `exists_prime_lsym` (Mathlib's CRT and Dirichlet), `lsym_recip_one` |
| 12 | L1061–1062 (S12 L381–394) | shape `(3^δ ∏ q_i^{u_i}, ∏ q_i^{v_i})` of a positive-second-coordinate class | gap filled | round-1 finding: asserted in tex. S12 derives it from the real place, even valuations at `2`, good primes and the image at `3`. Lean: `necAt_S12` (every condition proved) |
| 13 | L1063–1066 (S12 L396–407) | local equations `Ku + D_λ v = δλ`, `(K + D_s)v = 0`, `(λ+s)ᵗv = 0` | OK | rechecked bit by bit; Lean: `eqs_of_localBad`, `e4_of_mod3` (round 1) |
| 14 | L1068 (S12 L409–433) | "the matrix properties force `v = 0`, `δ = 0`, `u ∈ ker K`" | gap filled | round-1 finding: needs `K + Kᵗ = ssᵗ + D_s`, `sᵗ1 = 1`, `λᵗ1 = 0` and duality; S12 supplies exactly this (`ker N = ker Kᵗ ∩ s^⊥`). Lean: `kmat_forces` (round 1), `e3_of_e2` (S12 L416–418) |
| 15 | L1069–1073 (S12 L436–454) | `(β, 1)` local everywhere, independent of the torsion classes | gap filled | tex asserts; S12 checks each place. Lean: `cand_mem_S12` (all eight classes), `locM_cand`, `sqClass_at_bad`, `sqClass_three`, `localGoodUnram` |
| 16 | (S12 L337–345, L351–355) | `#E(ℚ_q)/2E(ℚ_q) = 4` at odd `q`; image at good `q` = unramified classes | OK | standard (formal group). Lean proves the consequence used, `localGoodUnram`, by another route: reduction to `𝔽_p` (ON THE SPOT, see Known issues 7) |
| 17 | (S12 L364–379) | 2-adic necessity: both coordinates have even valuation | OK | checked, including the `mod 8` step `u(ℓ+2u)(u+2ℓ) ≡ ℓ`. Lean: `locM_two_even`, `two_adic_odd` |
| 18 | L1076–1093 | lem:corank: full 2-torsion and `dim Sel₂ = 3` give corank 1 | OK (cited) | `r + dim Ш[2] = 1`; `dim F[2]` even by Cassels–Tate (Poonen–Stoll), so `F = 0`, `r + t = 1`. A cited leaf (`Lemma54`); not formalized |
| 19 | L1095–1106 | lem:forward-rank (BCDT Thm A + Kolyvagin Thm 1) | unverified | Kolyvagin is cited as the MPIM preprint MPI/90-69, not a refereed print; not read. Kato (L1103–1106) is used only for `r = 0`; not needed. Leaves `BCDTThmA`, `KolyvaginThm1` |
| 20 | L1107–1109 | "rank one and finite Ш, hence Ш[2] = 0" | OK | finiteness is not needed: `r = 1` and `r + dim Ш[2] = 1` give `Ш[2] = 0` (ON THE SPOT re-derivation, correction (c)); in Lean the Kummer map is onto by counting (`descentGlueM`, round 1) |
| 21 | L1110–1112 | the class is a rational point; abscissa class `β` | OK | Lean: `point_of_locM` (round 1) |
| 22 | L1112–1121 | rescaling to `E_{nH}`, the eleven witnesses, `w = (eHz)⁻¹`; `θ = 1` reuse | OK | Lean: `witnesses_of_points` (round 1) |

Round-1 findings, as rows: the representative shape (row 12), the matrix-forcing claim (row 14),
the Boolean-assignment sketch (row 10), Kolyvagin cited as a preprint (row 19). All four are
resolved (12, 14, 10 by S12 and Lean) or recorded (19).

## Known issues

1. **S11 is not available under that name** (tex L1033). S12's `par:descent` and
   `par:simultaneous-matrices` cover the whole construction that tex L1033–1074 delegates; S11 is
   not used.
2. **tex L1045–1047:** the vector `a` of the rank-one correction is undefined in the tex; S12
   L581–583 defines it.
3. **tex L1047:** the block is written `D₁`, which suggests a diagonal matrix; it is a general
   matrix `A` (S12 L641).
4. **tex L1055–1058** (row 10): "the determinant's full-product coefficient is one, thus a single
   Boolean assignment works on both supports" is right only because the toggled bits leave the
   smaller support's matrix unchanged (S12 L666). The tex does not say so.
5. **Kolyvagin** (tex L1100, bibitem L11163–11166) is a preprint; locator UNVERIFIED.
6. **Silverman's bibitem** (tex L11144–11145) lists "Chapters IV and VII"; the Kummer
   identification (`KummerSelmerM`) uses Chapter X (Prop. X.1.4, p. 315, as S12 L242 cites it;
   page UNVERIFIED). The manuscript itself never cites Chapter X in Section 5.
7. **ON THE SPOT proofs in this task** (both are standard and replace an S12 argument by an
   equivalent one; neither is built upon beyond its own statement):
   * `exists_toggle_injOn` (S12 L658–666): S12 uses the determinant as a multilinear polynomial;
     the Lean proof is an induction on the toggled set by a kernel argument.
   * `localGoodUnram` (S12 L337–355): S12 uses a formal subgroup of `E(ℚ_q)`; the Lean proof
     reduces to `𝔽_p`, where the Kummer map is onto by counting (`#E(𝔽_p)/2E(𝔽_p) = #E(𝔽_p)[2] = 4`),
     and lifts only the `x`-coordinate by Hensel's lemma.
8. **S12's global step** (S12 L455–525: `PointwiseTwoConverse` and the Cassels–Tate parity) and its
   pole formula (S12 L36–68) are not used, as instructed. The manuscript's own route (Lemma 5.4 then
   Theorem 5.3 then Lemma 5.5) is what is formalized.
9. **Route K reuse (correction (f)).** Nothing of `Slots/Multiplier`, `Slots/Theta` or
   `Config.monsky` is used, and none is imported directly. The import closure does contain them:
   the Route K square-class lemmas (`RouteK.Selmer.{Covering,PadicSquare,Two,Good}`, used for Hensel
   and `SqEq`) import `Hypotheses.CertifiedRank`, which imports `RouteK.Assembly.Realize`, which
   imports `RouteK.Slots` and `RouteK.System.Config`. Round 1's `KummerM`/`DescentM` (via
   `RouteK.Rank.Image`, `RK9`) have the same closure. If the revert of `Certificate/Parity` breaks
   that chain, the fix is a vendored copy of about fifteen Route K lemmas (listed in
   `scratch/pc-s12/log.md`).

## Statement checks (correction (a))

* **`Z2Corank`** (`SelmerTwoPower.lean`): `M ≃+ (Fin r → ℚ₂/ℤ₂) × F` with `F` finite. Since
  `Sel_{2^∞}(E/ℚ)` is a cofinitely generated `ℤ₂`-module (a theorem: `Sel_{2^∞}[2]` is a quotient
  of the finite group `Sel₂`, so the Pontryagin dual is finitely generated over `ℤ₂` by Nakayama),
  the structure theorem gives it the shape `(ℚ₂/ℤ₂)^t × F`, and `t` is unique. So `Z2Corank (selmerTwoPower E) 1`
  holds exactly when the true corank is `1`: the definition is faithful. Lemma 5.4 as a leaf at
  this predicate (`Lemma54`) is then true, by the structure theorem plus Cassels–Tate (Poonen–Stoll).
  STANDARD (not formalized).
* **`SelM` against the cohomological `Sel₂`** (new piece, flagged). `SelM ℓ` is the explicit
  2-Selmer system (pairs of squarefree integers, local Kummer images in x-form at `ℝ` and every
  `ℚ_p`). Tau Ceti's `selmerAt E 1` is the cohomological `Sel₂(E/ℚ)`. Their comparison is the
  hypothesis `KummerSelmerM : #Sel₂(E_ℓ/ℚ) = #SelM ℓ`: **textbook GLUE, not proved**. Tau Ceti's
  `TwoDescent.lean` proves one ingredient (the Kummer map of `[2]` read through a 2-torsion point is
  `x − e`), and `EtaleTwoDescent.lean` builds the cohomological descent map
  `H¹(G_K, E[2]) → (K[X]/(f))ˣ/squares` and proves that it agrees with the explicit map on Kummer
  classes (`cohomologicalMap_kummerMap`); its header says that the Selmer comparison "also needs its
  injectivity and the agreement of the local conditions, which are not proved". Those two facts,
  specialized to the split cubic of `E_ℓ` and to the x-form `LocM`, are what `KummerSelmerM` asks. Locator: Silverman, *The
  Arithmetic of Elliptic Curves*, 2nd ed., Prop. X.1.4 (as S12 L242 cites it). Silverman is in the
  manuscript's bibliography (Known issue 6). No count form is called "Theorem 5.3" here: `Lemma54At`
  at Silverman's `Sel₂` is Lemma 5.4 composed with this identification.

## Ratings of the new leaves

| leaf | kind | printed form? | reason |
| --- | --- | --- | --- |
| `Lemma54` | cited leaf, provenance (b) | the manuscript's `lem:corank`, verbatim in content | its proof cites Poonen–Stoll (Cassels–Tate); a consequence of published results, stated over genuine definitions (Tau Ceti's `Sel₂`, `SelmerCorankOne`) |
| `BCDTThmA` | printed leaf | consequence of the print | `IsModular` (written fresh: a weight-2 cusp form on `Γ₀(N)` whose `q`-expansion coefficients are `E.LFunction`'s) keeps less than the print (no newform, no level = conductor); locator UNVERIFIED |
| `KolyvaginThm1` | printed leaf | the `r = 1` case of the print as cited | includes `Ш(E/ℚ)` finite (Tau Ceti's Ш, `SelmerTwoPower.sha`), as the print does; preprint; UNVERIFIED |
| `MordellWeil` | textbook leaf | printed | unchanged from round 1 |
| `KummerSelmerM` | GLUE | no | textbook identification (Silverman X.1.4 plus the definitions); not a printed statement |

Kato (tex L1103–1106) is dropped (correction (b)): used only at `r = 0`. The modularity definition
is fresh; `GrossZagierModuli.lean` is not imported (checked: not in the import closure).

## The proof as formalized (new in round 2)

All files under `ZInQKernel/Contrib/OneProof/PoleS12/` (new), plus the final file.

1. **`MatrixRealization`** (S12 L543–683). `SharpAlg.lean`: `K` as `KS` on a finite support of
   naturals; `sharp_targets` (S12 L590–604); `sharp_ker_of_deleted` (L606–613);
   `exists_toggle_injOn` (L658–666); `block_injOn` (L631–652). `Convert.lean`: `Kmat ℓ` is `KS` on
   `ℓ.primeFactors` (`kmat_mulVec_eq`); `matrixConditions_of_KS`; residue-class parities; `lsym` of
   products. `Primes.lean`: `exists_prime_lsym` (CRT + Dirichlet, L668–679); `exists_aux_primes`
   (the slots `g b ≡ 1 (mod 12)` with columns `e_b + e_{b*}`). `Choice.lean`: `mc_of_choice`
   (`K1_B = 0` on both supports, L622–629, and the two targets). `Realization.lean`: the assembly.
2. **The dimension-three count** (S12 L300–454). `TwoAdic.lean`: necessity at `2`
   (L364–379). `NecS12.lean`: `necAt_S12`, with `b ≡ 1 (mod 4)` derived from `(K + D_s)v = σs`
   (L416–418). `Suff.lean`: the eight classes are torsion classes times squares at `2`, `3` and
   `q ∣ ℓ` (L436–454). `GoodF/` and `GoodUnram.lean`: unramified classes are local at good primes.
   `CountS12.lean`: `dimThreeCount_S12`.
3. **Lemmas 5.4, 5.5** (`Leaves.lean`): the leaves above, `lemma54At_of_printed`,
   `kolyvaginRankOne_of_printed`, and the support bound.

Correction (c) (ON THE SPOT, flagged in the docstrings of `KolyvaginThm1` and of the final
theorem): only `rank E_ℓ(ℚ) = 1` is used. With `#E_ℓ(ℚ)[2] = 4`, Mordell–Weil and `#SelM ℓ = 8`,
the Kummer map is onto by counting (`descentGlueM`), which is the re-derivation
`r + dim Ш[2] = 1` of tex L1107–1109 without finiteness of Ш.

## Correction (g): places that unfold `Manuscript.polePoly`, `PoleSoluble`, `PoleCompleteness`

None of the round-2 files unfolds them (the final theorems only name `Manuscript.PoleCompleteness`
as their type). Round 1's files do, in two places, to be re-checked after the rebase:

* `ZInQKernel/Contrib/PoleRC/Reduction.lean`, `poleCompleteness_of_crm` (L23–50): `intro B hden
  hpos hlt hS0` unfolds `Manuscript.PoleCompleteness`; `refine ⟨b, e, z, r₁, r₂, w, …⟩` unfolds
  `Manuscript.PoleSoluble`.
* `ZInQKernel/Contrib/PoleRC/Rescale.lean`, `polePoly_eq_zero_of` (L36–50): `simp only [polePoly]`
  unfolds `Manuscript.polePoly`.

## `#discharges` and autofold

`scratch/pc-s12/Discharges.lean` (imports `ZInQKernel.OneProof.Main`, `ZInQKernel.OneProof.Discharges`
and the final file) was run after `lake build` of the three modules (exit 0): "#discharges: 34
open hypotheses, 16366 theorems checked, 19 discharge one"; none of the 19 is a PoleRC/PoleS12
theorem (output: `scratch/pc-s12/discharges-output.txt`). VERIFIED. As in round 1,
`Manuscript.PoleCompleteness` is not a field of any bundle of `ZInQ.OneProof.frozenTarget`, so
nothing is discharged and autofold does not apply; `scratch/pc-s12/autofold.json` records the
statements with kinds and flags for a manuscript-faithful headline (issue #74).

## Files (round 2; all new, none imports `ZInQKernel.OneProof.Main`)

| file | content |
| --- | --- |
| `Contrib/OneProof/PoleCompletenessFromRCGenuine.lean` | final theorems: `poleCompleteness_of_restrictedConverseGenuine`, `…_abstract`, `dimThreeCount`, `simultaneousConstruction` |
| `PoleS12/SharpAlg.lean` | `𝔽₂` algebra: `KS`, `KSharp`, `sharp_targets`, `sharp_ker_of_deleted`, `exists_toggle_injOn`, `block_injOn` |
| `PoleS12/Convert.lean` | `kmat_mulVec_eq`, `matrixConditions_of_KS`, parities, `lsym_prod` |
| `PoleS12/Primes.lean` | `exists_prime_lsym` (CRT + Dirichlet), `exists_aux_primes` |
| `PoleS12/Choice.lean` | `mc_of_choice` |
| `PoleS12/Realization.lean` | `matrixRealization` |
| `PoleS12/TwoAdic.lean` | `locM_two_even`, `two_adic_odd` |
| `PoleS12/NecS12.lean` | `necAt_S12`, `e3_of_e2`, `mod4_of_e3` |
| `PoleS12/Suff.lean` | `locM_cand`, `sqClass_at_bad`, `sqClass_three`, `LocalGoodUnram`, `cand_mem_S12` |
| `PoleS12/CountS12.lean` | `dimThreeCount_S12` |
| `PoleS12/GoodF/KummerF.lean`, `GoodF/DescentF.lean` | Kummer maps and 2-descent over a field with `2, 3 ≠ 0`; `locM_finite` |
| `PoleS12/GoodUnram.lean` | `localGoodUnram` |
| `PoleS12/Leaves.lean` | `IsModular`, `BCDTThmA`, `KolyvaginThm1`, `Lemma54`, `KummerSelmerM`, `FullTwoTorsion`, `selM_finite` |

Round 1's uncommitted change to `PoleRC/Count.lean` (`NecAt`, class hypothesis in
`eqs_of_localBad`) did not compile at the start (unknown `hN`); it was finished and committed
(log, first entry).

## What remains

1. `KummerSelmerM` (GLUE): the identification of Tau Ceti's `Sel₂(E_ℓ/ℚ)` with `SelM ℓ`
   (Silverman X.1.4). Tau Ceti has the Kummer map through one 2-torsion point (`TwoDescent.lean`);
   the full comparison (the isomorphism `H¹(ℚ, E[2]) ≅ (ℚ*/ℚ*²)²`, its local versions and the local
   Kummer images) is a separate project.
2. The printed leaves `Lemma54`, `BCDTThmA`, `KolyvaginThm1`, `MordellWeil`, and Theorem 5.3.
