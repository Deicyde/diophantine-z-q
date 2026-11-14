# qm-split results log

Base cba8157f. Chain: leaf-fold4's olean chain (TailK), copied from leafq-check's ~/lqc-olean to ~/qms-olean;
check script `scratch/qm-split/chk.sh` (lean with leaf-fold4's LEAN_PATH). T0.lean: `import TailK` works (85 s cold).

Row sources (VERIFIED, read): definitions read in ~/dzq-wt/leaf-fold4/scratch/leaf-fold4/olean/*.lean
(the chain the frontier names for C4''), leafq-check rows in ~/dzq-wt/leafq-check/scratch/leafq-check/.

## H-46 `qmClassNumberOne`: PROVED, no leaf (VERIFIED, compiled)
- `scratch/qm-split/ClassNumberOne.lean` (import TailK): `HDec.QMSplit.CNO.qmClassNumberOne_proof :
  HDec.HSyn.G0Split.FibreQM.QMClassNumberOne` (the chain's own constant, imported). 0 errors, 8 s;
  `#print axioms` = [propext, Classical.choice, Quot.sound].
- Class number one computed: `euclid` (|nrd(x − q)| ≤ 7/8 by rounding in the basis 1, i, (1+j)/2, (i+k)/2;
  nrd = Eisenstein norm − 2·Eisenstein norm), `principal_of_lattice` (minimal |nrd| element of a left
  𝒪-stable subgroup I with dI ⊆ 𝒪 generates I). Eichler's theorem is no longer cited.
- Lattice glue: I = {x : ι(x)v ∈ Λ}; rank argument (Fin.cons family of 5 in rank-4 Λ), uniform denominator
  from `Submodule.annihilator_top_inter_nonZeroDivisors`; w = ι(α)v not c·real via finrank (range ≤ 2 < 4).

## H-35 `t27 : PkgI3.QMDichotomyYu`: PROVED from a published-form leaf (VERIFIED, compiled)
- `scratch/qm-split/YuLeaf.lean`: LEAF `HDec.QMSplit.Yu.YuThm11` (Yu 2013 Thm 1.1 as the locator audit read it:
  End⁰ ≅ B, or End⁰ ≅ M₂(ℚ(√d)), d < 0, with `ℚ(√d) ⊗ B ≅ M₂(ℚ(√d))`; the simple/non-simple labels of the
  cases dropped); `qmDichotomyYu_of_yu : YuThm11 → PkgI3.QMDichotomyYu` (drop the splitting clause).
  0 errors, 5 s, axioms standard.

## H-61 `QMAutCard`: PROVED from one leaf (VERIFIED, compiled)
- `scratch/qm-split/QMAut.lean`: LEAF `HDec.QMSplit.Aut.QMCentralizerCM` (End_𝒪(A) over ℚ̄ is ℤ or ≅ Φ⁻¹(𝒪) for an
  embedding Φ : k → B of an imaginary quadratic k; Shimura 1967, Jordan 1981 §3, González–Rotger 2006 §5;
  locators UNVERIFIED; printed over ℂ, ℚ̄ form via T11(b) flagged); `qmAutCard_of : QMCentralizerCM → HeckeRest.QMAutCard`.
  Axioms standard, 7 s.
- Computation: `disc_neg` (IsTotallyComplex ⇒ non-rational elements have t² < 4n), `unit_cases` (units of Φ⁻¹(𝒪):
  nrd = 1, trd ∈ ℤ), `card_units_R` (4/6/2 by explicit lists, `decide` on ℚ×ℚ lists), `excl_*` (products square
  to 3, 6, 18), `isoUnitEquiv : QMIso q q ≃ (com q)ˣ`.
