# sga1-etale results log

- Build tree: copied .lake/build and lean/.lake/build from ~/dzq-wt/pel-hodge (descends from dbf043a4);
  `lake build ZInQKernel.Contrib.OneProof.UniformizationTopology` OK (9052 jobs). VERIFIED
- Mathlib 4.35 has `RingHom.IsStandardSmooth.exists_etale_mvPolynomial` (RingTheory/RingHom/StandardSmooth.lean:257):
  standard smooth f ⇒ ∃ n g, g.comp C = f ∧ g.Etale (g : R[X_1..X_n] → S). So "standard smooth ⇒ étale over the
  polynomial ring in the free variables" is in the pin. VERIFIED (read)
- A.lean (compiled, no errors): `eval₂Hom_res`, `etale_res` (étale coordinates restrict to basic opens),
  `exists_etale_chart` (Smooth X.hom ⇒ every point has an affine U and f : Fin n → Γ(U) with
  eval₂Hom (algC X U) f étale), `exists_cPt_of_mem` (nonempty open of loc. finite type ℂ-scheme has a ℂ-point). VERIFIED
