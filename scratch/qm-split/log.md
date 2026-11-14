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

## H-63 `ALFixedPoints`: PROVED from the same leaf (VERIFIED, compiled)
- `QMAut.lean` §5-§6: `alFixedPoints_of : QMCentralizerCM → HeckeRest.ALFixedPoints`, axioms standard, 16 s total.
- AV glue `twist_data`: from G : (A, ι∘rep k) ≅ (A, ι): V = φ ι(τ), W = φ² in End_𝒪(A), V² = c W, W a unit
  (τ = i, j, ij; c = 2, −3, 6; `conjO_facts`).
- Computation: units w ∈ {±1, i-type, ζ₆, ζ₃} (`unit_cases'`); in each case V or V·w or V(1±w) squares to a
  forbidden value (non-square 2, 3, 6, 12 in an imaginary field; −2 via `no_sq_neg2`: 3c² = 2e² + 2b² + 6d²
  anisotropic, descent mod 3) or gives the CM element; m = 3: x ∈ 𝒪, x² = −3 ⇒ (1+x)/2 ∈ 𝒪
  (`half_mem_of_sq_neg3`, parity mod 2). The embedding check of the docstring (ℚ(√−2), ℚ(√−7), ... ) is
  replaced by these computations; ℤ case: v² = ±c impossible.

## H-42 `CMOptimalEmbedding`: PROVED from the same leaf (VERIFIED, compiled)
- `QMAut.lean` §7: `cmOptimalEmbedding_of : QMCentralizerCM → FS5NoCM.CMOptimalEmbedding`, axioms standard.
- Glue: ℤ case impossible (an order of finite index contains a non-rational element: `order_spans` via
  `exists_integral_multiple` + `AddSubgroup.nsmul_index_mem`); k case: R' ≅ com ≅ Φ⁻¹(𝒪) extends to
  fraction fields (`isFractionRing_of_mul_mem`, `IsFractionRing.ringEquivOfRingEquiv`), φ = Φ ∘ σ.

## H-2 `r4 : PkgI1.ThetaModularity`: SPLIT into two published-form leaves (VERIFIED, compiled)
- `scratch/qm-split/ThetaSplit.lean`: LEAFs `IgusaPsi4` (ψ₄ = 2⁻²Σθ⁸ weight 4 for Sp₄(ℤ)), `IgusaChi10`
  (χ₁₀ = −2⁻¹⁴∏θ² weight 10); `thetaModularity_of : IgusaPsi4 → IgusaChi10 → ThetaModularity` (constants
  cleared). Axioms standard, 4 s. Caveat in docstrings: Igusa defines ψ₄ as an Eisenstein series and prints
  the theta expression as a theorem (pages UNVERIFIED).

## H-86 `STQM`: PROVED from a published-form leaf (VERIFIED, compiled)
- `scratch/qm-split/STQM.lean`: row copied verbatim (leafq-check CMDescendsGlue.lean l.26-43, same namespace
  context and opens, in `…PeriodMapH.QMSplitSTQM`); LEAF `ShimuraTaniyamaQbar` (abelian surface over ℂ with a
  degree-4 field in End⁰ = ℚ ⊗ End has a model over ℚ̄; Shimura–Taniyama 1961 §12.4 Prop. 26, Shimura 1998,
  Milne CM notes §7; UNVERIFIED numbers; printed conclusion "model over a number field", ℚ̄-form = base change,
  flagged); `stqm_of : ShimuraTaniyamaQbar → STQM`, axioms standard, 11 s.
- Glue: E_d = ℚ(√2)(√d), d ∈ {−1, −3, −6} (AdjoinRoot tower, irreducible via a real embedding, finrank 4);
  √2 ↦ 1⊗ι(i), √d ↦ 1⊗ψ (ψ = φ or 2φ − 1) into the commutative subalgebra they generate;
  End⁰ ≠ 0 by flatness of ℚ over ℤ and injectivity of n ↦ ι(n).

## H-44 `ThetaRatiosAlgebraic`: SPLIT into 1 LEAF + 1 narrower GLUE (VERIFIED, compiled)
- `scratch/qm-split/ThetaRatios.lean`: LEAF `ThetaNullNonvanishing` (genus 2: at most one even θ-null vanishes;
  Mumford Tata II IIIa §8, Igusa 1962; UNVERIFIED); GLUE `ThetaFourthRatiosAlgebraic` (θ_m⁴/θ_{m₀}⁴ algebraic
  for period matrices of abelian surfaces over number fields; needs Appell–Humbert/GAGA/NS invariance and
  Thomae + Jacobi + Weil's dichotomy, or Shimura Duke 1976); `thetaRatiosAlgebraic_of`. Axioms standard, 5 s.

## H-87 `ValenceFormulaGammaStar`: SPLIT into 1 LEAF + 1 GLUE (VERIFIED, compiled)
- `scratch/qm-split/Valence.lean`: row + `ellOrder` copied verbatim (leafq-check Fold.lean l.466-497).
  LEAF `ValenceFormulaCocompact` (valence formula for any cocompact Fuchsian Γ ⊆ GL₂(ℝ)⁺ with volume = hyperbolic
  area of a fundamental domain, Mathlib's invariant measure on ℍ; Shimura 1971 Prop. 2.16/Thm 2.20, Rankin
  Thm 4.1.4; UNVERIFIED); genuine defs `IsCocompactFuchsian`, `IsFundDomain`, `ellOrderOf` (= `ellOrder` at Γ*
  by rfl); GLUE `GammaStarCocompactArea` (Γ* cocompact Fuchsian, fundamental domain of area π/6; needs Shimura
  §9.2, Shimizu's volume formula, index 4, or Takeuchi + Gauss–Bonnet); `valenceFormulaGammaStar_of`
  ((2m/4π)(π/6) = m/12). Axioms standard, 6 s.

## H-88 `QMHauptmodulBase3`: PROVED from 1 LEAF + 3 GLUE (+ bundle leaf r4) (VERIFIED, compiled)
- `scratch/qm-split/Haupt.lean`: leafq-check `Fold.lean` lines 1-934, 1326-2563 copied verbatim (row at
  `HDec.LeafQCheck.HM.QMHauptmodulBase3`), then `HDec.LeafQCheck.HM.QMSplit`:
  `qmHauptmodulBase3_of (hT : ThetaModularity) (hV : ValenceFormulaCocompactEq) (hA : GammaStarCocompactArea)
   (hC : ThetaQuotientValue24) (hD : EllipticOrderDvd) : QMHauptmodulBase3`; axioms standard; 24 s.
- LEAF `ValenceFormulaCocompactEq` (equality form + finitely many zero orbits + the ≤ clause; Shimura 1971 Thm 2.20).
  GLUE `GammaStarCocompactArea` (shared with H-87), `EllipticOrderDvd` (e_P ∣ ord_P F₁ when F₂(P) ≠ 0, same
  weight; textbook local expansion), `ThetaQuotientValue24` (jNum/jDen(Ω(i√(9+6√2))) = −16/27, numerically
  verified by leaf-review-a).
- Argument: H_c = 3779136·G20² − c·G8⁵ (weight 40, total 5/3); at i√3: e = 6, ord G8 = 2 (valence ≤ + e ≤ 6 +
  ord ≥ 2), G8 vanishes only on that orbit; ord G20 = a ≤ 4, ord H_c = 2a; other zeros contribute integers
  (EllipticOrderDvd with G8⁵) ⇒ a + 3N = 5 ⇒ N = 1: each fibre over c ∈ ℂ is one orbit; fibre over ∞ = orbit
  of i√3; continuity from the pole at i√3 and Γ*-invariance of jNum/jDen. G20 ≢ 0 from the CM value.
- Also `valenceFormulaGammaStar_of_eq`: H-87's row from the same leaf + glue.

## H-1, H-20, H-43, H-59 (moduli rows): witness splits (VERIFIED, compiled; logical assembly only)
- `scratch/qm-split/ModuliSplit.lean`: LEAF `CanonicalModelY3` (∃ fine witness of R1fpProps; Shimura 1967,
  Deligne 389 Thm 4.21; "qualified consequence" per audit). Universal GLUE Props over witnesses (published
  statement on the canonical model + transport): `HeckeOfFine` (pure project glue, Yoneda), `CoarseX6OfFine`
  (quotient + moduli + π₀(X₆)=1), `HauptmodulOfX6` (Baba–Granath Thm 2.1), `ReciprocityOfFine` (Shimura
  reciprocity), `ResidueOfX6` (González–Rotger Thm 5.12), `ConnectedOfFine` (Deligne π₀ + Galois action),
  `ShimuraFamily` (LEAF candidate: Shimura Main Thm I composed with every π) + `R1bTransport`, `ConicOfWitness`
  (Kurihara/Elkies + transport). Theorems: `r1r2fpRep_of`, `y3Connected_of` (+ converse `connectedOfFine_of`),
  `r1b_of`, `x6ConicModel_of` (from r1r2 + ConicOfWitness). Axioms standard, 5 s.
- Finding: a clause about one witness cannot be split into separately quantified published statements without
  a transport/uniqueness glue; the universal forms are GLUE by construction (stronger in form than the printed
  existence statements, equivalent given the comparison isomorphism).
- `EllipticOrderDvd` PROVED (VERIFIED, compiled): `ellipticOrderDvd_proof` (multiplier ζ = det/(cP+d)² is the
  derivative of the Möbius map at P (`Mb_sub_P`); F₁ = (z−P)^n g, invariance F₁(γz)F₂(z) = F₁(z)F₂(γz), limit
  z → P gives ζ^n = 1 (`zeta_pow_ord`); the multipliers form a finite subgroup H ≤ ℂˣ with |H| = e_P
  (`zeta_inj`, `zeta_congr`), cyclic, exponent = e_P ∣ n). `qmHauptmodulBase3_of'` : ThetaModularity →
  ValenceFormulaCocompactEq → GammaStarCocompactArea → ThetaQuotientValue24 → QMHauptmodulBase3. Axioms standard.
- `QMAut.lean` §8 (VERIFIED, compiled): LEAF `QMCentralizerCMC` (the same statement over ℂ, the printed
  setting) and `qmCentralizerCM_of : QMCentralizerCMC → T11b_Rigidity → QMCentralizerCM` (base change ℚ̄ → ℂ
  along `IsAlgClosed.lift`; End bijective by T11(b) + `endBC_injective`; centralizers correspond;
  `dim_baseChange`). `rows_of_C`: H-61 ∧ H-63 ∧ H-42 from QMCentralizerCMC + T11b. Axioms standard.

## Comparison isomorphism; HeckeOfFine and R1bTransport PROVED (VERIFIED, compiled)
- `ModuliSplit.lean` §Comparison: reducedness of smooth schemes over a domain (copied from model-glue
  `ModelGlue5.lean`, itself from smooth-fibre); `eq_id_of_fieldPts` (Mathlib's `ext_of_fromSpecResidueField_eq`;
  a self-map of a fine witness fixing all field points is 𝟙); `compare_iso` (two witnesses of R1fpProps are
  isomorphic compatibly with Φ: phi_part both ways); `heckeOfFine_proof` (twisted / right-multiplied universal
  families classified by R1univProps; inverse from twist α.symm, rightMul u⁻¹; `isoTwistSymm`, `isoRightMulOne`
  need maxHeartbeats 2·10⁶); `r1bTransport_proof`. `r1r2fpRep_of'` (H-1 without HeckeOfFine), `r1b_of'`
  (H-20 from ShimuraFamily alone). Axioms standard; 42 s.
