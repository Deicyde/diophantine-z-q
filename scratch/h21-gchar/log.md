# h21-gchar results log

Task: step (b) of the verdict on `h21C` (queue10): the Legendre-symbol genus character `gchar n (divSet n d₂)` used
in `quadPeriod` versus TYZ's `χ_{d₁,d₂}`.

## Setup
- Merged `origin/wip/h21c-steps` (h21S = `H21CSteps.TYZThm21Span`, `tyzThm21PairsC_of_span`).
- Build tree copied from `~/dzq-check2` (same `Main.lean`, base 4dfb7e583); `lake build
  ZInQKernel.Contrib.OneProof.TYZThm21Span` OK (FDelta 107 s, Span 13 s).
- `~/tyz-src/Period7.tex` is NOT on this host: every TYZ line number below is taken from the project notes
  (h33-sign.md, h29-proof.md, rv-tyz-inputs.md), marked UNVERIFIED here.

## Existing inputs found (VERIFIED, read in the tree)
- `ZInQKernel/OneProof/TYZSplit.lean`: `ClG n = Gal(H_n/K_n)`, `art n : Pic(O_K) ≃* ClG n` (Tau Ceti
  `ringClassArtinEquiv`), `IsExtChar n e χ` (χ is the character of `K_n(√e)`), `isExtChar_chiT`,
  `isExtChar_unique`, `prod_pstar_divSet`, `map_divSet`, `coe_chiT`.
- `ZInQKernel/Contrib/OneProof/TYZGenusFold/Jacobi.lean`: `jacobiSym_neg_absNorm` (`(−n/N I) = 1` for `N I`
  prime to `2n`), `gchar_univ_mk0`, `sgn2_ofAdd`.
- `ZInQKernel/RouteK/Redei/Genus.lean`: `chi_mk0`, `exists_mk0_coprime` (one prime `q`).

## Step 1: GChar.lean (VERIFIED, compiled 11-17 ~02:45, `lake env lean`, 0 errors, no sorry)
`scratch/h21-gchar/GChar.lean`, namespace `ZInQ.Contrib.H21GChar`; imports `OneProof.TYZSplit`,
`Contrib.OneProof.TYZThm21Span`, `Contrib.OneProof.TYZGenusFold.Jacobi`. Output: `GChar-output.txt`.
- `dstar d = if d % 4 = 1 then d else −d`; `dstar_eq_neg_one_pow` (= (−1)^((d−1)/2) d for odd d); `dstar_mul`;
  `jacobiSym_dstar`: (d*/m) = (m/d) for odd d, m (Mathlib reciprocity).
- `IsTYZChi n d₂ χ := IsExtChar n (dstar d₂) χ` (χ on Gal(H_n/K_n) is the character of K_n(√d₂*));
  `tyzChi n d₂` (choice; 1 if none); `tyzChiCl n d₂ t := tyzChi n d₂ (art n t)`.
- `isTYZChi_chiT`, `isTYZChi_unique`, `tyzChi_eq_chiT`.
- **`tyzChiCl_eq_gchar`**: Odd n → Squarefree n → d₂ ∣ n → tyzChiCl n d₂ t = gchar n (divSet n d₂) t.
- `exists_mk0_coprime'` (every class has an ideal of norm prime to M > 1); `gchar_mk0_eq_jacobiSym`
  (N𝔞 prime to 2d₂ ⇒ gchar(T(d₂))[𝔞] = (d₂*/N𝔞)); `IsTYZChiNorm`; `isTYZChiNorm_unique`; `isTYZChiNorm_gchar`;
  `isTYZChiNorm_tyzChiCl`; `jacobiSym_d₁_side` ((D₁/N𝔞) = (d₂*/N𝔞), D₁ = d₁* (n≡3 mod 4), −4d₁* (n≡1 mod 4)).
- `quadPeriodTYZ`, `quadPeriodTYZ_eq`; `TYZThm21SpanG`, `TYZThm21PairsG`; `tyzThm21Span_of_G`,
  `tyzThm21SpanG_of_span`, `tyzThm21PairsC_of_G`, `tyzThm21PairsG_of_pairsC`, `tyzThm21PairsG_of_spanG`;
  `TYZThm21SpanG₁` (character of K_n(√d₁*)), `tyzThm21SpanG_iff_swap`.
- `#print axioms` (8 theorems): [propext, Classical.choice, Quot.sound].
