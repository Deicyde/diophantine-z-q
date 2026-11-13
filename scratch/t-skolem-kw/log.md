# t-skolem-kw results log

## T13 Skolem–Noether — PROVED (VERIFIED, compiled)
- File: `scratch/t-skolem-kw/SkolemNoether.lean` (imports only Mathlib).
- Statements copied verbatim: `PkgI6.SkolemNoether` (as `TSkolemKW.SkolemNoether`),
  `HSyn.SkolemNoether` (as `HSynSkolemNoether`), `LeafSkolemNoether` (automorphism case).
- Theorems: `TSkolemKW.skolemNoether : SkolemNoether`, `hsynSkolemNoether`, `leafSkolemNoether`.
- `lake env lean` 2026-11-12 22:2x: no errors; `#print axioms`: propext, Classical.choice, Quot.sound.
- Auxiliary results proved: `isSimpleRing_tensor` (C central simple, B simple ⇒ C ⊗[K] B simple;
  no finiteness needed), `nonempty_linearEquiv_of_finrank_eq` (modules over a simple Artinian
  K-algebra with equal finite K-dimension are isomorphic).
- Mathlib v4.35.0 has no Skolem–Noether and no simplicity of tensor products (grep, VERIFIED).
  ATLAS (`~/aq/atlas-lean`, `MathlibExt.Algebra.Central.SkolemNoether.skolem_noether`) has the
  automorphism case only; not copied (own proof, general two-map form).
