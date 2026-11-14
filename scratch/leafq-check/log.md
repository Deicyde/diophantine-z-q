# leafq-check results log

Base 67c2daf9. Candidates (leaf-fold4 §2.3 LEAF?): thetaRatiosAlgebraic, qmHauptmodul, x6ConicModel,
y3Connected, cmDescends, gammaStarGen, valenceBoundGammaStar. Source of the statements:
scratch/leaf-fold4/Leaves4.lean (lines: QMHauptmodul 358, ThetaRatiosAlgebraic 43228, X6ConicModel 75669,
Y3Connected 97479, ValenceBoundGammaStar 113443, CMDescends 114469, GammaStarGen 117339).

## GammaStarGen: plan of a direct proof (computations VERIFIED in py/)
- y = i+j ∈ 𝒪 (y² = −1, fixed point of ι(x₄)); pure elements v of 𝒪 with v² = −1 ↔ points of the
  hyperboloid −2b²+3c²−6d² = 1; ⟨v,y⟩ = −2b+3c = cosh d(v,y) (`py/gsg_enum.py`).
- the four nearest orbit points u_k = s_k⁻¹ y s_k, s = x₆, x₆⁻¹, x₆x₄, (x₆x₄)⁻¹ (`py/gsg_words.py`);
  ⟨v,u_k⟩ − ⟨v,y⟩ = b+3d, b−3d, −5b+6c+3d, −5b+6c−3d.
- certificate: 3·nrd(v) − ⟨v,y⟩² = (b+3d)(−5b+6c−3d) + (b−3d)(−5b+6c+3d) (`py/gsg_dir.py`: the
  Dirichlet cone of the four is compact, vertices at cosh = √3, the order-6 points).
- upper sheet: pairY(x y x̄) − nrd x = 12((b−c)²+d²) (`py/gsg_sym.py`).
- base: x commutes with y ⇒ x = a + b y; u = x j x⁻¹ has imJ = 1 + 4b²/N, imK = 2ab/N (N = a²+b²)
  (`py/gsg_norm.py`); integrality forces ab = 0 or a = ±b, i.e. x ∈ ℚ^×⟨x₄⟩.
- normalizer witnesses for x₄, x₆ (`py/gsg_norm.py`).

## GammaStarGen: PROVED (VERIFIED, compiled)
- `scratch/leafq-check/GammaStarGen.lean`: `import Mathlib` only; PkgI1 §1-§2, `x4`, `x6`, `GammaStarGen`
  copied verbatim from Leaves4.lean; `theorem gammaStarGen_proof : GammaStarGen`.
- `lake env lean scratch/leafq-check/GammaStarGen.lean`: 0 errors (linter warnings only);
  `#print axioms gammaStarGen_proof` = [propext, Classical.choice, Quot.sound]. ~90 s.
- No leaf, no glue hypothesis: the LEAF? field `gammaStarGen` of `OpenAddedLeaves4` can be removed
  (period-glue's `s8WeightExact_of hT gammaStarGen_proof`).

## Fold over leaf-fold4's chain (VERIFIED)
- `scratch/leafq-check/Fold.lean` (`import TailK`; `chk.sh` = lean with leaf-fold4's chain oleans copied to
  ~/lqc-olean and leaf-fold4's lake LEAN_PATH): the same proof proves the chain's own constant
  `HDec.HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen`; `HDec.HSyn.sixContactMin_of_open5` (bundle
  `OpenAddedLeaves5` = OpenAddedLeaves4 without `gammaStarGen`, 19 fields): 0 errors, axioms standard,
  `example : … → _root_.ZInQ.SixContactMin` compiles. 11 s. Count 66 → 65 (26 + 19 + 19 + 1).

## ValenceBoundGammaStar: split (VERIFIED, compiled)
- `scratch/leafq-check/ValenceBound.lean` (import Mathlib; PkgI1 §1-§2, `U`, `ValenceBoundGammaStar` verbatim):
  `ellOrder P` (= Nat.card of the Möbius maps of the stabilizer of P in Γ*), `ValenceFormulaGammaStar`
  (LEAF: Σ_T ord_P/e_P ≤ m/12, valence formula + signature (0;2,4,6)), `EllipticOrderLe6`
  (0 < e_P ≤ 6), `valenceBound_of : ValenceFormulaGammaStar → EllipticOrderLe6 → ValenceBoundGammaStar`
  (the valence count), 0 errors, axioms standard.

## EllipticOrderLe6: PROVED (VERIFIED, compiled)
- `ValenceBound.lean`: `ellipticOrderLe6_proof : EllipticOrderLe6` (crystallographic restriction:
  ζ = det γ/(cP+d)² = μ̄/μ, |ζ| = 1, 2Re ζ = 4re(x)²/nrd(x) − 2, and 4re²/nrd = trace of Ad(x) on 𝒪 ∈ ℤ
  (`adTrace_int`, identity checked in `py/vb_adtrace.py`); ζ ∈ {±1, ±i, ±1/2 ± i√3/2}; ζ multiplicative
  and injective on the stabilizer; (±1/2 ± i√3/2)(±i) has real part ±√3/2, not among the eight).
- `valenceBound_of_formula : ValenceFormulaGammaStar → ValenceBoundGammaStar`. Axioms standard.
- Fold.lean: `OpenAddedLeaves6` (valenceBoundGammaStar → valenceFormulaGammaStar), `sixContactMin_of_open6`
  compiles over the chain (11 s), axioms standard.
