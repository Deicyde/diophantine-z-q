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
  one leaf** `QMCentralizerCM` (`End_𝒪(A)` is `ℤ` or an optimally embedded `Φ⁻¹(𝒪)`): the automorphism counts,
  the Atkin–Lehner fixed points and the optimal-embedding statement are computations in `B` and in imaginary
  quadratic fields.
* **Reduced to published leaves plus smaller named glue:** H-44 (1 leaf + 1 glue), H-87 (1 leaf + 1 glue),
  H-88 (1 leaf + 3 glue, two of them shared or numeric; the Hauptmodul property is now *proved* from the
  valence formula), H-1, H-20, H-43, H-59 (the existence leaf plus per-clause transport glue).

| row | old form | new leaves (published form, source) | new glue | Lean proof |
|---|---|---|---|---|
| H-46 `qmClassNumberOne` | consequence of Eichler's class number one | none | none | `ClassNumberOne.lean`: `HDec.QMSplit.CNO.qmClassNumberOne_proof` |
| H-35 `t27 : QMDichotomyYu` | consequence of Yu Thm 1.1 (splitting clause dropped) | `YuThm11` (Yu, JPAA 2013, Thm 1.1, with the clause `ℚ(√d) ⊗ B ≅ M₂(ℚ(√d))`; case labels dropped) | none | `YuLeaf.lean`: `HDec.QMSplit.Yu.qmDichotomyYu_of_yu` |
| H-61 `QMAutCard` | composite (Shimura 1963, Rotger 2003) | `QMCentralizerCM` (Shimura 1967 §§1-3, Jordan 1981 §3, González–Rotger 2006 §5) | none | `QMAut.lean`: `HDec.QMSplit.Aut.qmAutCard_of` |
| H-63 `ALFixedPoints` | composite (Ogg, Rotger 2004, embedding check) | `QMCentralizerCM` | none | `QMAut.lean`: `alFixedPoints_of` |
| H-42 `cmOptimalEmbedding` | consequence of Shimura 1967 / Jordan | `QMCentralizerCM` | none | `QMAut.lean`: `cmOptimalEmbedding_of` |
| H-86 `STQM` | consequence of Shimura–Taniyama | `ShimuraTaniyamaQbar` (Shimura–Taniyama 1961 §12.4 Prop. 26; Milne, CM notes §7: CM abelian varieties over `ℂ` are defined over `ℚ̄`; specialized to a degree-4 field in `End⁰`) | none | `STQM.lean`: `…PeriodMapH.QMSplitSTQM.stqm_of` |
| H-2 `r4 : ThetaModularity` | consequence of Igusa's transformation formula | `IgusaPsi4`, `IgusaChi10` (Igusa, AJM 84 (1962), 86 (1964), 89 (1967)) | none | `ThetaSplit.lean`: `HDec.QMSplit.Theta.thetaModularity_of` |
| H-44 `thetaRatiosAlgebraic` | composite (Shimura 1976, Mumford, Igusa) | `ThetaNullNonvanishing` (genus 2: at most one even theta-null vanishes; Mumford Tata II IIIa §8, Igusa 1962) | `ThetaFourthRatiosAlgebraic` (θ⁴ ratios algebraic; NS/GAGA + Thomae/Jacobi or Shimura 1976) | `ThetaRatios.lean`: `…ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of` |
| H-87 `ValenceFormulaGammaStar` | consequence of the valence formula + signature `(0;2,4,6)` | `ValenceFormulaCocompact` (Shimura 1971 Prop. 2.16/Thm 2.20; Rankin Thm 4.1.4; any cocompact Fuchsian `Γ`, volume = Mathlib's hyperbolic area of a fundamental domain) | `GammaStarCocompactArea` (Γ* cocompact Fuchsian with a fundamental domain of area `π/6`) | `Valence.lean`: `…QMSplitVB.valenceFormulaGammaStar_of`; also `Haupt.lean`: `valenceFormulaGammaStar_of_eq` |
| H-88 `QMHauptmodulBase3` | composite (Hauptmodul property + value `−16/27`) | `ValenceFormulaCocompactEq` (same sources, equality form) | `GammaStarCocompactArea` (shared with H-87), `EllipticOrderDvd` (`e_P ∣ ord_P` for invariant quotients; textbook), `ThetaQuotientValue24` (the number `j_θ(i√(9+6√2)) = −16/27`) | `Haupt.lean`: `HDec.LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of` (uses the bundle leaf `r4`) |
| H-1 `r1r2 : R1R2fpRep` | composite (Shimura 1967, Deligne 389, Baba–Granath, González–Rotger) | `CanonicalModelY3` (∃ fine witness; Shimura 1967 Main Thms I-II, Deligne 389 Thm 4.21) | `HeckeOfFine` (project, Yoneda), `CoarseX6OfFine`, `HauptmodulOfX6` (Baba–Granath Thm 2.1), `ReciprocityOfFine` (Shimura reciprocity), `ResidueOfX6` (González–Rotger Thm 5.12), each = published statement + transport to every witness | `ModuliSplit.lean`: `HDec.QMSplit.Moduli.r1r2fpRep_of` |
| H-59 `Y3Connected` | composite (Deligne π₀ + orbit computation) | `CanonicalModelY3` | `ConnectedOfFine` (Deligne 389 §§2-3 + transport; equivalent to the row given the leaf) | `ModuliSplit.lean`: `y3Connected_of`, `connectedOfFine_of` |
| H-20 `r1b` | project glue (triple chosen from `r1r2`) | `ShimuraFamily` (LEAF candidate: Shimura 1967 Main Thm I composed with every `π : Y → P¹`) | `R1bTransport` (project: comparison isomorphism of fine witnesses) | `ModuliSplit.lean`: `r1b_of` |
| H-43 `x6ConicModel` | consequence (Kurihara 1979, Elkies 1998) | uses `r1r2` (H-1) | `ConicOfWitness` (Kurihara/Elkies + transport, or Kummer theory from the clause list) | `ModuliSplit.lean`: `x6ConicModel_of` |

(Report sections 2-6 follow.)
