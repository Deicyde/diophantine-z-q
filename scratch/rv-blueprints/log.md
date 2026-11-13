# rv-blueprints results log

## 18:15-18:20 Compile audit (VERIFIED, compiled)
Each blueprint Lean file copied to `Audit_<name>.lean` with `audit_tail.lean` appended (an `elab`
command that runs `Lean.collectAxioms` on every declaration added by the file and reports any
axiom other than propext, Classical.choice, Quot.sound). Runner `run_audit.sh` (sequential, one
Lean process). Outputs in `audit_out/`.

| file | exit | errors | warnings | sorry | declarations audited | non-standard axioms |
| --- | --- | --- | --- | --- | --- | --- |
| bp-faltings/Hodge | 0 | 0 | 0 | 0 | 125 | none |
| bp-faltings/Models | 0 | 0 | 0 | 0 | 40 | none |
| bp-modcurves/Gamma1Genus | 0 | 0 | 0 | 0 | 44 | none |
| bp-modcurves/TateNormalForm | 0 | 0 | 0 | 0 | 12 | none |
| bp-modcurves/Jacobian | 0 | 0 | 0 | 0 | 38 | none |
| bp-modcurves/ModularCurveDefs | 0 | 0 | 0 | 0 | 20 | none |
| bp-modcurves/AnalyticModuli | 0 | 0 | 0 | 0 | 16 | none |
| bp-modcurves/PointTransport | 0 | 0 | 0 | 0 | 70 | none |
| bp-qmmoduli/QMOrder | 0 | 0 | 21 (linter) | 0 | 81 | none |
| bp-qmmoduli/Units72 | 0 | 0 | 0 | 0 | 7 | none |
| bp-qmmoduli/QMAbVar (imports ZInQKernel.HDecomp.A6.A6, prebuilt) | 0 | 0 | 9 (linter) | 0 | 176 | none |

Warnings are unused-tactic / deprecated `push_neg` linter warnings only.
(First run failed only in the appended audit command: a `MessageData` numeral typing slip,
fixed by `let mut n : Nat := 0`; the blueprint files themselves compiled in that run too.)

## 18:40 AT3 normalization check (VERIFIED, computed: at3_check.py, at3_check.out)
faltingsHeightEC(y^2 = x^3 + 1) by direct 2-d integration = -1.3211174284280; the eta-product
form -(1/12)log(|eta(rho)|^24 (Im rho)^6) - log 2pi gives the same to 19 digits. Deligne's
recalled minimum -0.74875248 (STANDARD, locator UNVERIFIED) minus (1/2)log pi = -1.3211174229
(agrees to the 8 digits of the recalled constant). So faltingsHeightEC is Faltings-normalized
and h_D = h_F + (1/2) log pi at g = 1.

## 18:55 §2.2 sign check of bp-qmmoduli (VERIFIED, computed: sheet_check.py, sheet_check.out)
B = (2,-3) in M2(R) (i -> diag(√2,-√2), j -> [[0,1],[-3,0]]; relations asserted), μ = 2j + ij,
μ² = -6 asserted. For 30 random J with J² = -1 (16 on the sheet c > 0, 14 on c < 0), the form
x ↦ E0(xJ, x), E0(x,y) = trd(μ⁻¹ x ȳ), is negative definite on the sheet c > 0 (eigenvalues in
[-50.8, -0.028]) and positive definite on c < 0 (eigenvalues in [0.063, 46.7]). So exactly one
sign of ±E0 is a Riemann form for each complex structure, as bp-qmmoduli §2.2 claims.

## 19:00 Findings (statements; details in docs/research/rv-blueprints.md)
- F-a (bp-faltings) inf definition: correct in Faltings' normalization (Néron mapping property
  for every smooth O_L-scheme ⇒ ω_N ⊆ ω_G ⇒ h(G) ≥ h(N_L) ≥ h(N_L') = h_st). STANDARD argument.
- F-b R18, R20, R21, R22 hold for h_F as stated whatever the paper's normalization (directions:
  upper bounds on h_F follow from bounds on h_D ≥ h_F; R20 is a difference; R21: (1/2)log(2π²)
  = 1.4913 < 3/2; R22: log π = 1.1447 < 3). R19 is the one normalization-sensitive leaf: a
  consequence only if Gaudron–Rémond's h is original-Faltings (as locators.md read).
- F-c AT1's right side faltingsHeightEC is the same integral formula; the external normalization
  check is AT3 (re-verified here). No acceptance test exercises g ≥ 2 against an independent
  value: add additivity h(E1×E2) = h(E1)+h(E2) (H7) as AT4.
- M-a (bp-modcurves) IsJacobian is a universal property over genuine objects; JacobianExists
  is Milne/Weil's existence theorem; neither vacuous nor a disguised conclusion.
- M-b MC9 ("our model ≅ Shimura's canonical model") is a leaf over an object the blueprint does
  not define; unnecessary because the existential R16 is invariant under ℚ-isomorphism of J.
- Q-a (bp-qmmoduli) N5 as printed DOES use the moduli scheme over a base (Buzzard's model over
  ℤ[1/30], universal abelian scheme, N5 L443-530); the verdict holds for h-trust's route only.
- Q-b R5fp (degree form) is too weak for A10 (rv-h-cm §7.2): case D(R) ≠ 1 needs k ⊆ ℚ(x);
  counterexample to sufficiency: R = O of Q(√-19), h = 1, D(R) = 6, #CM = 4 = |W-orbit|,
  [ℚ(x):ℚ] = 2 = [ℚ(i):ℚ]. Also NoCM step 2 (twist constants) needs exact fields at t = 1, ∞.
- Q-c R1an (pointwise) too weak for F1: the Hauptmodul comparison needs every τ to occur and
  τ ↦ π(P_τ) holomorphic.
- Q-d Lemma NV step 4 (h-b1) needs X6 geometrically connected and W-Galois (h-b1 M10, π0 = 1);
  no field-point leaf of bp-qmmoduli supplies π0.
