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
