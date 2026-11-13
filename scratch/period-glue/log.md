# period-glue results log

Task period-glue, 2026-11-13. Base 6f296292 + merge of origin/wip/period-map (already contained).
Targets: period-map's glue `S8Nonzero`, `S8WeightExact`, `SphereFactorAffine`,
`BaseChangeClassUnique`, `PiTwistC`, `QMTwistLattice`; restate leaves `ValenceBoundGammaStar`,
`CMDescends`.

## Setup
- `build_base.sh`: `PGBase.lean` = fibre-qm-period FibreQM.lean lines 1-20634 + part_fqm.lean +
  period-map part_light/theta/siegel/order/heavy (verbatim; = period-map's DevHeavy without the
  import). `run_base1.txt`: 0 errors, 3m13s. VERIFIED.
- prereq `lake build ...QMLattice ...JHeight ...HeightConstant ...Objects`: OK 1m25s (`run_prereq.txt`).

## BaseChangeClassUnique — PROVED (VERIFIED, run_bcu.txt)
- `BCU.lean`: `PeriodGlue.baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique`.
  Axioms `[propext, Classical.choice, Quot.sound]`.
- Inputs: Mathlib only; rigidity `isMonHom_of_geometricallyIntegral` copied verbatim from
  scratch/mul-rigidity/Rigidity.lean (namespace renamed `PeriodGlue.MulRigidity`).
- Proof: comparison map from the pullback property; every compatibility checked after composing
  with `g'` (`eq_of_comp`); level clause at `a = 0` gives identity → identity; rigidity.

## QMTwistLattice — REDUCED (VERIFIED, run_qmtwist.txt)
- `QMTwist.lean`: `qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg) : QMTwistLattice`.
  Axioms standard.
- `T11aRiemannHom`: LEAF (textbook; T11a with `Hom A A'` for `End A`; Mumford §1 + GAGA,
  Birkenhake–Lange Prop. 1.2.1, UNVERIFIED locators). `t11aRiemannEnd_of_hom` proves the kernel's
  `T11aRiemannEnd` from it (so it is no stronger than needed beyond the Hom generalization).
- `QMLatticeTwistAlg`: GLUE, pure algebra (twist relation on QM lattices ⇔ `τ' ∈ Γ*τ`).

## PiTwistC — REDUCED (VERIFIED, run_pitwist.txt)
- `PiTwist.lean`: `piTwistC_of (h1 : R1fpProps) (h2 : R2fpProps) (hT : TwistOrbitFinite Y Φ)
  (hF : FibreTransferC Y π) : PiTwistC Y Φ π`. Axioms standard.
- `TwistOrbitFinite`: GLUE (moduli): twist relation on ℚ̄- and ℂ-points = orbits of a finite set
  of automorphisms of Y.
- `FibreTransferC`: GLUE (AG, Jacobson): fibres of π = G-orbits on ℚ̄-points ⇒ on ℂ-points, for Y
  proper smooth over ℚ. Finding: without the properness/smoothness hypotheses the transfer is false
  (Y = Spec ℂ has no ℚ̄-points), so they are part of the statement.

## S8Nonzero — REDUCED to an explicit matrix; certificate computed (VERIFIED, run_s8.txt)
- `S8.lean` (imports `PGLight` = period-map's PMLight.lean verbatim, `build_light.sh`):
  `omega_cm4 : PkgI1.Omega (√2 + I) = Omega0 = !![(-1+I)/2, 1; 1, -1+I]` (proved);
  `s8Nonzero_iff : S8Nonzero ↔ S8Omega0` (`S8Omega0 := thetaSum8 Omega0 ≠ 0`). Axioms standard.
- Numerics (`py/s8_value.py`, `py/s8_exact.py`, mpmath 60 digits, VERIFIED):
  Ω(√2+i) = [[(-1+i)/2, 1],[1,-1+i]], Im Ω = diag(1/2, 1);
  θ_m(Ω0)^8 / ϑ00(i)^16 ∈ {−1/4 (×4), −1 (×4), −4 (×1), 0 (×1, char ((1,1),(0,0)))};
  Σθ⁸(Ω0) = −9 ϑ00(i)^16 = −33.90792957610492455716… (ϑ00(i) = π^{1/4}/Γ(3/4));
  each θ_m(Ω0) = u·ϑ[a1,b1+a2]((−1+i)/2)·ϑ[a2,b2+a1](−1+i), u ∈ {1, −i};
  rigorous tail bound per theta for truncation |n_k| ≤ 2: < 2.18·10⁻⁴ (mpmath iv).

## S8WeightExact — REDUCED to ThetaModularity (leaf) + GammaStarGen (leaf candidate) (VERIFIED, run_w8.txt)
- `W8.lean`: `s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) : S8WeightExact`.
  Axioms standard. No glue left.
- Proved: `G8AutoSubgroup` (cocycle of denom; scalars `g8Auto_scalar`); modular embedding of
  g4 = ι(1+i+j), g6 = ι((j−3)/2): M4, M6 ∈ Sp4(ℤ) (`M4_symp`, `M6_symp`), Ω(gτ) = M·Ω(τ)
  (`spAct_of_poly` + `I1_g4`, `I1_g6`), det g·det(CΩ+D)(τ−3)(τ+1) = −(cτ+d)²(gτ−3)(gτ+1)
  (`spFactor_of_poly` + `I2_g4`, `I2_g6`).
- `py/modemb.py` (sympy exact): M matrices found via y = xu with yμȳ = nrd(x)μ (symplectic lattice
  map); Ω(gτ) = M·Ω(τ) exact; factor ratio ±1 (also for μ = 2j+ij: ratio +1).
- `py/triangle.py`: x2 = (3/2)i + 2j + (1/2)ij (trd 0, nrd 6) has x2·x4 = −3 + j = 2·x6, so
  g6 g4⁻¹ is of order 2 in PSL2; fixed points √2+i, i√3; cosh d = √3 (by hand, see GammaStarGen).
- `GammaStarGen`: LEAF candidate (published signature (0;2,4,6) + Poincaré polygon theorem +
  covolume); flagged for human check.
