# rleaf-elliptic results log

Base 322303a2 (wip/integrate-w39). Start 2026-11-13 06:42 PST.

## Step 1. Vendoring (VERIFIED)
- Closure of oct16 `TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure`:
  212 modules (46,658 lines), 20 already vendored (all from 5a01f5fe), 192 new
  (`vendor-new.txt`). Copied by tcport.py from ~/tc-oct16 (5a01f5fe3621), unchanged.
- `lake build ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure`:
  OK, 3892 jobs, 0 errors (`build1.txt`, 1m23s wall).
- NOTICE: one source entry added. diffcheck2: IDENT 1587, NOTE-ONLY 0, MOD-NOTED 29, MOD-UNNOTED 0.

## Step 2. T36 proved (VERIFIED, compiled)
- File `ZInQKernel/Contrib/RLeaf/T36Torsion.lean`.
- `ZInQ.RLeaf.t36_torsionStructure : X1Belyi.TorsionStructure` (exact leaf type, no hypotheses).
- `ZInQ.RLeaf.nTors_eq_torsionBy : X1Belyi.nTors W N = AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)`.
- `lake build ZInQKernel.Contrib.RLeaf.T36Torsion`: OK. `#print axioms` for both:
  [propext, Classical.choice, Quot.sound].
