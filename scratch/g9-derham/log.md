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

## 03:3x-04:3x compiled layers (all `lake env lean`, exit 0, no errors)
- Speiser.lean: `speiser_finrank` (dim_K M = [L:K]·dim_K M^Γ for semilinear Γ = Gal(L/K) action).
- Descent.lean: `Dsp act ρ S` (S-equivariant maps V → B); `descent_finrank`:
  dim Dsp(ker γ) = [L:K]·dim Dsp(G) given γ : G ↠ Gal(L/K), ι : L →ₐ B semilinear.
- Galois.lean: `range_gfToGqp : (gfToGqp p F).range = (gammaF p F).ker` for F/ℚ_p finite Galois,
  `fieldF p F ⊆ ℚ̄_p` a copy of F (`finrank_fieldF`, IsGalois instance).
- OverF.lean: `overF_count`: C ⊗_K V ≅ U × U equivariant, Dsp(V) ≠ 0 ⇒ [C:K]·dim Dsp(V) = 2·dim Dsp(U).
- Local.lean: `htMult_eq_one_of_R10` (G9 HT part): from `DeRhamComparison` (R10) and G8's local
  output (F/ℚ_p finite Galois, A/F with dim 2, e : C ⊗ V_p(A) ≃ₗ[C] C² × C² G_F-equivariant via
  `gfToGqp`), `htMult p r 0 = 1 ∧ htMult p r (-1) = 1`. T23, T10 not used.
- FINDING (VERIFIED by reading the Lean): R10's Lean form gives only the multiplicities at 0 and −1
  (`htMultOver … 0 = g`, `… (−1) = g`), not the vanishing at other weights; so `HasHTWeights p r
  {0, −1}` (all w) does not follow from R10 as stated. Also htMultOver is a truncated division;
  the F'-structure on htSpaceOver (`finrank_dvd_Dsp`) makes it exact.
