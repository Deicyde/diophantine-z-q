# g9-derham results log

## 2026-11-13 03:1x PST: route check
- VERIFIED (read): h-decomposition.md §1 "Recommendation: route P for the announced decomposition,
  route K as the fallback" (about line 466); the glue table row G9 (line 1035) is on route P;
  route K (GK1, GK2) replaces G9 only on the fallback route. So G9 is still needed.
- VERIFIED (read): manuscript L10939-11000, Lemma `lem:de-rham-descent` (K/ℚ_ℓ, F/K finite, A/F
  abelian surface, r : G_K → GL₂(C_ℓ), V_ℓ(A) ⊗ C_ℓ ≅ r|G_F ⊕ r|G_F ⇒ r de Rham, HT weights 0, −1).
- VERIFIED (read): h-trust C3 "Galois choice": N5 applies the lemma with K = ℚ₅, and F may be
  taken Galois over ℚ_ℓ.
- VERIFIED (read): R10 = `PkgI4.DeRhamComparison` is stated directly for `V_p(A)` (pkg-I3's
  `galRep`), so T10 (`T10_TateDuality`, an `opaque` placeholder) carries no content and is not
  needed as a hypothesis.

## 03:15 I4Layer.lean
- `ZInQKernel/Contrib/G9/I4Layer.lean`: verbatim copy of Leaves.lean L3230-4735 (PkgI4Sec), in
  namespace `ZInQ.Contrib.G9`. VERIFIED: `lake env lean` exit 0, no errors (1m44s);
  `lake build ZInQKernel.Contrib.G9.I4Layer` OK.
