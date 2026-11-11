# wk-h log

## Step 1 (2026-11-11): read sources
- Read h-trust.md §§0-2 (36 steps A1-A10, B1-B3, C1-C10, D1-D5, E1-E4, F1-F4), HeightMin.lean,
  Height.lean, h-map.md §1.

## Step 2: Mathlib v4.35 inventory (grep of .lake/packages/mathlib/Mathlib)
- Present: Height/{Basic,NumberField,Projectivization,MvPolynomial,EllipticCurve}: Weil heights
  `Height.logHeight` (ι → K, K number field), `absLogHeight₁`, `logHeight_eval_le`
  (homogeneous degree-N map: h(p(x)) ≤ log max(bound,1) + N h(x)), `logHeight_eval_ge`
  (Nullstellensatz certificate ⇒ lower bound). ModularForms: CongruenceSubgroups (Gamma1),
  CuspForm, QExpansion, LFunction; HeckeRing/Defs (abstract). AlgebraicGeometry/Group/Abelian
  (proper geom. integral group schemes are commutative). FieldTheory/AbsoluteGaloisGroup;
  ContCohomology (+ Sha); Algebra/BrauerGroup/Defs (CSA classes); RingTheory/Perfectoid/BDeRham.
- Absent (0 hits): Skolem–Noether, Chebotarev, Tate module, Néron model, Faltings height,
  Artin/Swan conductor, Hilbert symbol, de Rham / Hodge–Tate representations, Hecke operators
  on modular forms, newforms, Galois representations attached to modular forms, Shimura curves.
- N5 L858-964 read: proof factors through h_F(A): (A–D) ⇒ A is an L'-isogeny factor of J₁(N),
  N ≤ QM², [L':ℚ] ≤ QM; (E) ⇒ h_F(A) ≤ Q¹⁷M²⁴; (F) ⇒ h(u) ≤ 10¹³ max(1,h_F(A)).
- J(u) = −57600 F(u)²/G(u)⁶ (scratch/h-b1/b1_checks.py l.20).

## Step 3: F4 certificate (scratch/wk-h/f4_cert.py, output f4_cert.output.txt)
- Res(F,G) = 4081466880000000000 = 2^18 3^13 5^10.
- 3x^7 = A1 F_h + B1 G_h, 104976000000 y^7 = A2 F_h + B2 G_h, A_i, B_i integer binary forms of
  degrees 1, 5 (ℓ¹ norms 20333129, 184047851). VERIFIED (sympy expand = 0).
- Consequence (argument, to be checked in Lean): for coprime a,b, gcd(F_h(a,b),G_h(a,b)) divides
  3·2^10 3^8 5^6, and 12 h(u) ≤ h(J(u)) + c with c ≈ 300 (N5 F4: h(u) < h(j) + 74).

## Step 4: Tier-1 draft scratch/wk-h/BackToU.lean
- Imports ZInQKernel.Hypotheses.Height only (upstream package lean/ not built here, so
  HeightMin cannot be imported); states SixContactMinAt S (SixContactMin = SixContactMinAt
  Mult.S_mul by rfl).
- `lake env lean scratch/wk-h/BackToU.lean`: compiles, 9 s; one sorry (twelve_mul_ratHeight_le,
  F4). Proved: cert_x, cert_y (ring), G_ne_zero, sixContactMin_of_jHeightBound (nlinarith).

## Step 5: Tier-2 draft scratch/wk-h/Arakelov.lean
- Signature `ArakelovSig` (AV over bundled number fields, dim, hF, Isog/deg, prod, J1, jQM,
  theta nulls); Prop fields Javanpeykar (Thm 1.1.1 at X₁(N)), GaudronRemond (Thm 1.4),
  FaltingsVariation (Lemma 5 + additivity), BostLower (GR14 §9), Pazuki (Cor 1.3(2), g=r=2),
  IgusaLY (LY eqs (2),(13),(14), LNY §2.2); residual ModularLevelBound S (A1-E1).
- `transfer_numerics` (E3-E4 arithmetic, N5 L868-905): PROVED (no sorry).
- `jHeightBound_of_sig`: sorry (assembly; needs F2 via logHeight_eval_le and height invariance
  of ℚ-points under extension).
- `lake env lean scratch/wk-h/Arakelov.lean`: compiles, ~13 s, one sorry warning.
