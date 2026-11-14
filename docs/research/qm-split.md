# qm-split: the Shimura-curve, QM and theta rows of the frontier, split into published forms

Task qm-split, 2026-11-14. Base cba8157f (fork main after w54 and frontier r3). Lean: `scratch/qm-split/`
(results log `log.md`; check script `chk.sh`, which runs `lean` over leaf-fold4's olean chain `TailK`, the
chain that the frontier's rows are stated in). No file under `ZInQKernel/`, `blueprint/`, or another task's
notes or scratch was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no
network here; every theorem number below is UNVERIFIED unless marked otherwise).

## 1. Main result

All 14 rows now have a compiled Lean proof from stated hypotheses (no `sorry`; every `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`, VERIFIED).

* **Proved outright, no leaf:** H-46 `qmClassNumberOne`. Class number one of `𝒪` is a computation: `𝒪` is
  left norm-Euclidean (`|nrd(x − q)| ≤ 7/8`), so Eichler's theorem is no longer cited.
* **Proved from published-form leaves only:** H-35 `QMDichotomyYu` (Yu Thm 1.1 with its splitting clause),
  H-2 `ThetaModularity` (Igusa's `ψ₄` and `χ₁₀`), H-86 `STQM` (Shimura–Taniyama), and **H-42, H-61, H-63 from
  one leaf** `QMCentralizerCMC` (`End_𝒪(A)` over `ℂ` is `ℤ` or an optimally embedded `Φ⁻¹(𝒪)`) and the bundle
  leaf T11(b): the automorphism counts,
  the Atkin–Lehner fixed points and the optimal-embedding statement are computations in `B` and in imaginary
  quadratic fields.
* **H-87 `ValenceFormulaGammaStar` from published leaves only**: the valence formula applied to `Γ¹ = ι(𝒪¹)`
  and Shimizu's covolume `2π/3`; the passage to `Γ*` (index 4, distinct and covering cosets, orbit counting
  `r e* = 4 e¹`) is compiled.
* **H-88 `QMHauptmodulBase3` from the same two leaves, the bundle leaf `r4` (= H-2's Igusa leaves) and one
  number**, `j_θ = −16/27` at the CM point of discriminant −24: the Hauptmodul property is *proved* from the
  valence formula, and the divisibility of orders at elliptic points is proved.
* **Reduced to published leaves plus smaller named glue:** H-44 (1 leaf + 1 glue), H-1, H-20, H-43, H-59 (the
  existence leaf plus per-clause published statements stated for every witness; **the comparison isomorphism of two fine
  witnesses is now compiled** (`compare_iso`), which proves the project glue `HeckeOfFine` and `R1bTransport`:
  H-20 rests on one leaf candidate only).
* `QMCentralizerCM` (over `ℚ̄`) is itself proved from its printed form over `ℂ` (`QMCentralizerCMC`) and the
  bundle's textbook leaf T11(b) (`T11b_Rigidity`), so H-42, H-61, H-63 rest on `QMCentralizerCMC` + T11(b).

| row | old form | new leaves (published form, source) | new glue | Lean proof |
|---|---|---|---|---|
| H-46 `qmClassNumberOne` | consequence of Eichler's class number one | none | none | `ClassNumberOne.lean`: `HDec.QMSplit.CNO.qmClassNumberOne_proof` |
| H-35 `t27 : QMDichotomyYu` | consequence of Yu Thm 1.1 (splitting clause dropped) | `YuThm11` (Yu, JPAA 2013, Thm 1.1, with the clause `ℚ(√d) ⊗ B ≅ M₂(ℚ(√d))`; case labels dropped) | none | `YuLeaf.lean`: `HDec.QMSplit.Yu.qmDichotomyYu_of_yu` |
| H-61 `QMAutCard` | composite (Shimura 1963, Rotger 2003) | `QMCentralizerCMC` (over `ℂ`: Shimura 1967 §§1-3, Jordan 1981 §3, González–Rotger 2006 §5) + bundle leaf `T11b_Rigidity` | none | `QMAut.lean`: `HDec.QMSplit.Aut.qmAutCard_of` (from the `ℚ̄` form), `rows_of_C` |
| H-63 `ALFixedPoints` | composite (Ogg, Rotger 2004, embedding check) | same | none | `QMAut.lean`: `alFixedPoints_of`, `rows_of_C` |
| H-42 `cmOptimalEmbedding` | consequence of Shimura 1967 / Jordan | same | none | `QMAut.lean`: `cmOptimalEmbedding_of`, `rows_of_C` |
| H-86 `STQM` | consequence of Shimura–Taniyama | `ShimuraTaniyamaQbar` (Shimura–Taniyama 1961 §12.4 Prop. 26; Milne, CM notes §7: CM abelian varieties over `ℂ` are defined over `ℚ̄`; specialized to a degree-4 field in `End⁰`) | none | `STQM.lean`: `…PeriodMapH.QMSplitSTQM.stqm_of` |
| H-2 `r4 : ThetaModularity` | consequence of Igusa's transformation formula | `IgusaPsi4`, `IgusaChi10` (Igusa, AJM 84 (1962), 86 (1964), 89 (1967)) | none | `ThetaSplit.lean`: `HDec.QMSplit.Theta.thetaModularity_of` |
| H-44 `thetaRatiosAlgebraic` | composite (Shimura 1976, Mumford, Igusa) | `ThetaNullNonvanishing` (genus 2: at most one even theta-null vanishes; Mumford Tata II IIIa §8, Igusa 1962) | `ThetaFourthRatiosAlgebraic` (θ⁴ ratios algebraic; NS/GAGA + Thomae/Jacobi or Shimura 1976) | `ThetaRatios.lean`: `…ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of` |
| H-87 `ValenceFormulaGammaStar` | consequence of the valence formula + signature `(0;2,4,6)` | `ValenceFormulaCocompactEq` (Shimura 1971 Prop. 2.16/Thm 2.20; Rankin Thm 4.1.4; any cocompact Fuchsian `Γ`, volume = Mathlib's hyperbolic area of a fundamental domain; only its `≤` clause is used here) applied to `Γ¹`; `ShimizuCovolumeO1` (`ι(𝒪¹)` cocompact with covolume `2π/3`; Shimura 1971 Prop. 9.2, Shimizu 1965) | none (the index argument is compiled) | `Haupt.lean`: `HDec.LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_O1`; older routes `Valence.lean` (`…_of_shimizu`, with the glue `GammaStarFromO1`) |
| H-88 `QMHauptmodulBase3` | composite (Hauptmodul property + value `−16/27`) | `ValenceFormulaCocompactEq`, `ShimizuCovolumeO1`; bundle leaf `r4` | `ThetaQuotientValue24` (the number `j_θ(i√(9+6√2)) = −16/27`); `EllipticOrderDvd` stated and **proved** | `Haupt.lean`: `HDec.LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_O1` |
| H-1 `r1r2 : R1R2fpRep` | composite (Shimura 1967, Deligne 389, Baba–Granath, González–Rotger) | `CanonicalModelY3` (∃ fine witness; Shimura 1967 Main Thms I-II, Deligne 389 Thm 4.21) | `CoarseX6OfFine`, `HauptmodulOfX6` (Baba–Granath Thm 2.1), `ReciprocityOfFine` (Shimura reciprocity), `ResidueOfX6` (González–Rotger Thm 5.12), each = published statement for every witness; `HeckeOfFine` stated and **proved** | `ModuliSplit.lean`: `HDec.QMSplit.Moduli.r1r2fpRep_of'` |
| H-59 `Y3Connected` | composite (Deligne π₀ + orbit computation) | `CanonicalModelY3` | `ConnectedOfFine` (Deligne 389 §§2-3 + transport; equivalent to the row given the leaf) | `ModuliSplit.lean`: `y3Connected_of`, `connectedOfFine_of` |
| H-20 `r1b` | project glue (triple chosen from `r1r2`) | `ShimuraFamily` (LEAF candidate: Shimura 1967 Main Thm I composed with every `π : Y → P¹`) | none: `R1bTransport` stated and **proved** (the comparison isomorphism `compare_iso` is compiled) | `ModuliSplit.lean`: `r1b_of'` |
| H-43 `x6ConicModel` | consequence (Kurihara 1979, Elkies 1998) | uses `r1r2` (H-1) | `ConicOfWitness` (Kurihara/Elkies + transport, or Kummer theory from the clause list) | `ModuliSplit.lean`: `x6ConicModel_of` |


**Leaf inventory** (the published statements these 14 rows now rest on; all locators UNVERIFIED):

| leaf | statement | source | rows |
|---|---|---|---|
| `YuThm11` | QM abelian surface over an algebraically closed field of char 0 (indefinite `B`): `End⁰ ≅ B` or `M₂(ℚ(√d))`, `d < 0`, splitting `B` | Yu, JPAA 2013, Thm 1.1 | H-35 |
| `QMCentralizerCMC` | over `ℂ`: `End_𝒪(A)` is `ℤ` or `≅ Φ⁻¹(𝒪)` for an embedding `Φ` of an imaginary quadratic field | Shimura 1967; Jordan 1981 §3; González–Rotger 2006 §5 | H-42, H-61, H-63 (with T11(b)) |
| `ShimuraTaniyamaQbar` | an abelian surface over `ℂ` with a degree-4 field in `End⁰` has a model over `ℚ̄` | Shimura–Taniyama 1961 §12.4; Milne, CM notes §7 | H-86 |
| `IgusaPsi4`, `IgusaChi10` | `2⁻²Σθ⁸`, `−2⁻¹⁴∏θ²` are Siegel modular of weight 4, 10 for `Sp₄(ℤ)` | Igusa 1962, 1964, 1967 | H-2, H-88 |
| `ThetaNullNonvanishing` | genus 2: at most one even theta-null vanishes | Mumford, Tata II; Igusa 1962 | H-44 |
| `ValenceFormulaCocompactEq` | valence formula for cocompact Fuchsian groups (hyperbolic area of a fundamental domain) | Shimura 1971 Prop. 2.16, Thm 2.20; Rankin Thm 4.1.4 | H-87, H-88 |
| `ShimizuCovolumeO1` | `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` | Shimura 1971 Prop. 9.2; Shimizu 1965 | H-87, H-88 |
| `CanonicalModelY3` | the level-3 QM moduli problem has a fine witness (`R1fpProps`) | Shimura 1967; Deligne 389 Thm 4.21 | H-1, H-59 (H-43 via `r1r2`) |
| `ShimuraFamily` (candidate) | Shimura's holomorphic `φ : ℍ → Y₃(ℂ)` composed with every `π : Y₃ → P¹` | Shimura 1967 Main Thm I; Deligne 389 §4.15 | H-20 |

Remaining glue: `ThetaFourthRatiosAlgebraic` (H-44), `ThetaQuotientValue24` (H-88, one number), and the
per-witness statements `CoarseX6OfFine`, `HauptmodulOfX6`, `ReciprocityOfFine`, `ResidueOfX6` (H-1),
`ConnectedOfFine` (H-59), `ConicOfWitness` (H-43).

Counts (strict rule: LEAF = published form). Before: 14 GLUE rows. After: 1 row is a theorem with no
hypothesis (H-46); 6 rows are theorems from published-form leaves only (H-2, H-35, H-42, H-61, H-63, H-86;
5 new leaves `IgusaPsi4`, `IgusaChi10`, `YuThm11`, `QMCentralizerCMC`, `ShimuraTaniyamaQbar`, plus the
existing bundle leaf T11(b)); H-87 is a theorem from 2 published leaves (`ValenceFormulaCocompactEq`,
`ShimizuCovolumeO1`); H-88 from those, `r4` and one number (`ThetaQuotientValue24`); H-20 rests on one leaf
candidate (`ShimuraFamily`); H-44 rests on `ThetaNullNonvanishing` + one composite glue
(`ThetaFourthRatiosAlgebraic`); H-1, H-43, H-59 rest on `CanonicalModelY3` + per-witness published statements.

New theorems that discharge glue (all compiled): `qmClassNumberOne_proof`, `ellipticOrderDvd_proof`,
`compare_iso` (uniqueness of the fine witness), `heckeOfFine_proof`, `r1bTransport_proof`,
`qmCentralizerCM_of` (the `ℂ`-leaf gives the `ℚ̄`-form via T11(b)), `coset_cover`, `coset_distinct`,
`kept_eq`, `gammaStarValence_of_O1` (the valence formula for `Γ*` from the one for `Γ¹`).

## 2. The computations (proved, no leaf)

* **Class number one** (`ClassNumberOne.lean`). In the basis `1, i, (1+j)/2, (i+ij)/2` of `𝒪`,
  `nrd(a + bi + c(1+j)/2 + d(i+ij)/2) = N(a,c) − 2N(b,d)` with `N(x,y) = x² + xy + y²`. Rounding `c, d` then
  `a, b` gives `−(2·1/4 + 6·1/16) ≤ nrd(x − q) ≤ 1/4 + 3·1/16`, so `|nrd(x − q)| ≤ 7/8` (`euclid`), so a left `𝒪`-stable subgroup
  `I` with `dI ⊆ 𝒪` is `𝒪α` for an `α` of minimal `|nrd|` (`principal_of_lattice`). The lattice step: for
  `0 ≠ v ∈ Λ`, `I = {x : ι(x)v ∈ Λ}` has `Λ = ι(I)v` (5 vectors in a rank-4 lattice), a uniform denominator
  (annihilator of the torsion quotient), and `w = ι(α)v` is not `c·(real)` since `Λ` spans `ℂ²` over `ℝ`.
  VERIFIED (compiled, 8 s).
* **Units, fixed points, optimal embeddings** (`QMAut.lean`). For `R = Φ⁻¹(𝒪) ⊂ k` imaginary quadratic: a
  non-rational element of `k` has negative discriminant (`disc_neg`, from `IsTotallyComplex`: otherwise a
  complex embedding is real); a unit `u` of `R` has `nrd Φ(u) = 1` and integral trace, so `u = ±1` or a root
  of `x² + 1`, `x² ∓ x + 1`; hence `#Rˣ = 4, 6, 2` (explicit lists, `decide` on `ℚ × ℚ`), and two CM types
  never coexist (products square to `3, 6, 18`). `Aut(A, ι) ≃ End_𝒪(A)^×`. Atkin–Lehner: from
  `(A, ι ∘ rep k) ≅ (A, ι)` one gets `V = φι(t)`, `W = φ²` in `End_𝒪(A)` with `V² = cW` (`c = 2, −3, 6`), and
  in each unit case `V`, `Vw` or `V(1 ± w)` squares to a forbidden value or is the CM element; `x² = −2` has
  no solution in `B` (`3c² = 2e² + 2b² + 6d²`, descent mod 3), and `x ∈ 𝒪`, `x² = −3` forces `(1+x)/2 ∈ 𝒪`
  (parity). The optimal-embedding row extends `R' ≅ Φ⁻¹(𝒪)` to fraction fields. VERIFIED (17 s).
* **Elliptic orders** (`Haupt.lean`, `ellipticOrderDvd_proof`). At a fixed point `P` of `γ`, the multiplier
  `ζ = det γ/(cP + d)²` is the derivative of the Möbius map; `F₁ = (z − P)^n g` and the invariance of
  `F₁/F₂` give `ζⁿ = 1`; the multipliers form a finite (cyclic) subgroup of `ℂˣ` of order `e_P`, so
  `e_P ∣ n`. VERIFIED.
* **From `Γ¹` to `Γ*`** (`Haupt.lean` §Index). `Γ¹ = ι(𝒪¹)` is normal in `Γ*`; the representatives
  `ι(1), ι(a4), ι(a6), ι(a4a6)` (norms `1, 2, 3, 6`) lie in distinct cosets (a trivial Möbius action forces a
  scalar matrix, so a norm ratio `2, 3, 6, 12, 18` would be a square) and cover `Γ*` (the chain's normalizer
  descent with representatives `{1, i, j, ij}`, rewritten through `i a4⁻¹, j a6⁻¹, ij (a4a6)⁻¹ ∈ 𝒪`); for each
  `z` the points `g_i z` form `r_z` classes under `Γ¹` with `r_z e*_z = 4 e¹_z` (injections between the classes
  and `Stab*(z)/Stab¹(z)`); orders and `e¹` are constant along `Γ*`-orbits. So the valence formula for `Γ¹`
  (total `m/3`) gives the bound, the equality and the representatives for `Γ*` (total `m/12`).
* **The Hauptmodul property** (`Haupt.lean`, `fibre_c`, `jth_fibre`, `jth_continuous`). With
  `H_c = 3779136·G20² − c·G8⁵` (weight 40, total `5/3`): `e = 6` and `ord G8 = 2` at `i√3` (valence bound for
  `G8`, `ord ≥ 2`, `e ≤ 6`), `G8` vanishes only on that orbit, `ord G20 = a ≤ 4`, `ord H_c = 2a` there,
  every other zero contributes an integer, so `a + 3N = 5` forces `N = 1`: each fibre of `j_θ` over `ℂ` is one
  `Γ*`-orbit; the fibre over `∞` is the orbit of `i√3`; continuity from the pole at `i√3` and invariance.

## 3. The remaining glue (named, each with what it needs)

| glue | rows | statement | what it needs |
|---|---|---|---|
| `ThetaFourthRatiosAlgebraic` | H-44 | `θ_m(Ω)⁴/θ_{m₀}(Ω)⁴` algebraic for period matrices of abelian surfaces over number fields | the polarization defined by `Ω` is algebraic and defined over `ℚ̄` (Appell–Humbert, GAGA, `NS(A_ℚ̄) = NS(A_ℂ)`); Thomae (Mumford Tata II IIIa §8), Jacobi, Weil's dichotomy; or Shimura, Duke 43 (1976) |
| `ThetaQuotientValue24` | H-88 | `jNum/jDen(Ω(i√(9+6√2))) = −16/27` | Baba–Granath's CM values of the Hauptmodul with Igusa's theta expressions of the Igusa invariants; numerically VERIFIED by leaf-review-a |
| `CoarseX6OfFine`, `HauptmodulOfX6`, `ReciprocityOfFine`, `ResidueOfX6`, `ConnectedOfFine`, `ConicOfWitness` | H-1, H-59, H-43 | each clause, for every witness | the published statement on the canonical model (Baba–Granath Thm 2.1; Shimura reciprocity; González–Rotger Thm 5.12; Deligne's `π₀`; Kurihara/Elkies) **plus** the transport to an arbitrary witness: for fine witnesses the comparison isomorphism is now compiled (`compare_iso`), so what remains of the transport is the invariance of each clause under it; for coarse witnesses (`X₆`) a comparison is still needed (`CurveBijIso`-type glue) |

## 4. Findings

1. **No row statement is false, vacuous or stronger than its sources** among the 14 (each is now proved from
   hypotheses whose statements were checked here, §1). One reading issue: H-35's row drops Yu's splitting
   clause; the leaf keeps it.
2. **A row about one witness cannot be split into separately quantified published statements without a
   uniqueness of the witness.** For H-1, H-20, H-43, H-59 the per-clause Props are universal over witnesses.
   The uniqueness of the fine witness is now **compiled** (`compare_iso`: two witnesses of `R1fpProps` are
   isomorphic compatibly with `Φ`; this is `PinUnique` without `π`, which the chain had left as an argued,
   uncompiled statement), and it proves `HeckeOfFine` (twisted universal families, `R1univProps`) and
   `R1bTransport` outright. An alternative split of H-1's `π₀` clause exists in the chain:
   `Pi0X6.r1pi0Props_of_X6Props` (from `R5ptProps`, `R5fpCount`, `R2X6CMExact`, `AGInputs`).
3. **Class number one needs no citation**: the order is norm-Euclidean with constant `7/8`.
4. **The Hauptmodul property is a consequence of the valence formula** for the two theta forms already in the
   chain (`G8`, `G20`); the covolume of `Γ*` is not needed as an input (Shimizu's covolume of `𝒪¹` and a
   compiled index argument suffice); only the value at the third branch point is genuinely a separate input.
6. **Reuse.** `ModuliSplit.lean`'s reducedness lemma for smooth schemes is copied from model-glue (which copied
   smooth-fibre); `Haupt.lean`'s base and the rows `STQM`, `ValenceFormulaGammaStar` are leafq-check's text.
5. **Leaf statements and their form** (each docstring gives the source; all theorem numbers UNVERIFIED):
   `YuThm11` drops the simple/non-simple labels (weaker); `IgusaPsi4`, `IgusaChi10` are the modularity of
   Igusa's forms with their theta expressions (Igusa prints the expression as a theorem about the Eisenstein
   series; flag); `ShimuraTaniyamaQbar` specializes "CM" to a field of degree `2g` in `End⁰` and states the
   model over `ℚ̄` (Milne's form; Shimura–Taniyama print a model over a number field, from which the `ℚ̄`
   model is a base change, not compiled); `ThetaNullNonvanishing` drops the identification of the two cases;
   `ValenceFormulaCocompact(Eq)` uses Mathlib's invariant measure on `ℍ` and a genuine fundamental-domain
   predicate; `CanonicalModelY3`, `ShimuraFamily` keep the audit's "qualified consequence" caveat (Lemma QP).

## 5. Files and checks (all VERIFIED: compiled with `scratch/qm-split/chk.sh`, axioms standard)

| file | content | time |
|---|---|---|
| `ClassNumberOne.lean` | H-46 | 8 s |
| `YuLeaf.lean` | H-35 | 5 s |
| `QMAut.lean` | H-61, H-63, H-42; `QMCentralizerCMC` → `QMCentralizerCM` | 16 s |
| `STQM.lean` | H-86 (row copied verbatim from leafq-check) | 12 s |
| `ThetaSplit.lean` | H-2 | 4 s |
| `ThetaRatios.lean` | H-44 | 5 s |
| `Valence.lean` | H-87 (row copied verbatim from leafq-check) | 5 s |
| `Haupt.lean` | H-88 and H-87 (leafq-check `Fold.lean` lines 1-934, 1326-2563 copied verbatim, then qm-split's section): `ellipticOrderDvd_proof`, the index argument, `qmHauptmodulBase3_of_O1`, `valenceFormulaGammaStar_of_O1` | 26 s |
| `ModuliSplit.lean` | H-1, H-59, H-20, H-43; `compare_iso`, `heckeOfFine_proof`, `r1bTransport_proof` | 43 s |

Each file ends with `#print axioms` lines and, for chain constants, an `example` with fully qualified names.
The olean chain is leaf-fold4's (`~/qms-olean`, a copy of leafq-check's `~/lqc-olean`), as for leafq-check.

## 6. What remains

* The glue of §3. For the moduli rows the next piece is a comparison of coarse witnesses (`X₆`), which with
  `compare_iso` would reduce the remaining universal Props to their published statements plus invariance
  checks.
* Folding: the theorems are over leaf-fold4's chain constants (C4'' keeps them); `STQM`, `ValenceFormulaGammaStar`,
  `QMHauptmodulBase3` are leafq-check's constants, copied verbatim here (the fold must identify the copies).
* `ShimuraTaniyamaQbar` could be restated with a model over a number field and the `ℚ̄` form proved by base
  change (not done).
