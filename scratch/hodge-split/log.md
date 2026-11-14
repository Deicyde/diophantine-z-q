# hodge-split results log

Task hodge-split, 2026-11-14. Base cba8157f. Lean checks: `lake env lean scratch/hodge-split/<file>.lean`
after `lake build ZInQKernel.Contrib.R10.Amend ZInQKernel.Contrib.AbVarBC.Dim` (both built 03:40, exit 0).

## H-52 `G0Galois.FiniteImageHT` (FiniteImage.lean)
- Row copied verbatim from scratch/leaf-fold5/Leaves5.lean l.50965 (objects from ZInQKernel/Contrib/G9/I4Layer.lean).
- LEAVES: `TateTwistInvariants` (Tate 1967 §3.3 Thm 2, K finite over ℚ_p inside ℚ̄_p), `AxSenTate`
  (Tate 1967 §3.3 Thm 1 / Sen 1969 / Ax 1970). Locators UNVERIFIED (no source on host).
- PROOF `finiteImageHT_of_tate : TateTwistInvariants → AxSenTate → G0Galois.FiniteImageHT`.
  Steps: open kernel (continuity of Mathlib's absoluteGaloisGroup.map, closed finite-index ⇒ open,
  krullTopology_mem_nhds_one_iff_of_normal), finite coefficient field (adjoin of the finitely many
  entries; g9-derham's `liftGL`), finite descent (g9-derham's `descent_finrank`, Speiser — replaces
  Hilbert 90 of the row's citation).
- COMPILED 03:50: axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- File renamed FiniteImage.lean → HodgeSplit.lean (single growing file; scratch files cannot import each other).

## H-8 `ZInQ.Contrib.R10.DeRhamComparisonHT` (HodgeSplit.lean §6)
- Row imported from ZInQKernel/Contrib/R10/Amend.lean (unchanged).
- LEAVES: `HodgeTateDecompAbVar` (ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g, G_F-equivariant, g = dim A; Fontaine 1982
  Invent. 65 / Tate 1967 §4 / Faltings 1988; UNVERIFIED locators; bases chosen), `TateTwistInvariants`,
  `AxSenTate` (shared with H-52), `DeRhamH1AbVar` (IsDeRhamOver of V_p(A): "H¹_ét = V_p(A)^∨ is de Rham",
  Faltings 1989/Tsuji/Scholze Cor 1.8; H¹_ét replaced by V^∨ since étale cohomology is not in Mathlib).
- GLUE proved: `range_gfToGqp_eq` (image of G_F is G_{F'} for any finite F, not only Galois),
  `htSpaceOver_eq_map` (Hom_{G_F}(V, ℂ_p(j)) ≅ (ℂ_p(j−1)^{G_F})^g × (ℂ_p(j)^{G_F})^g through e),
  `htMultOver_of_decomp` (multiplicity g·([w=0]+[w=−1])), `dim_finite_I4` (abvar-bc's dim_finite transported).
- PROOF `deRhamComparisonHT_of_leaves : HodgeTateDecompAbVar → TateTwistInvariants → AxSenTate →
  DeRhamH1AbVar → ZInQ.Contrib.R10.DeRhamComparisonHT`. COMPILED 04:30, standard axioms. VERIFIED.

## H-32 `∀ p, PkgI4.T23_FontaineClosure p` (HodgeSplit.lean §7)
- Row imported (ZInQKernel/Contrib/G9/I4Layer.lean l.1488, unchanged).
- New genuine definitions: `ddrStd ρ` = (B_dR ⊗ ℚ_pⁿ)^{G_{ℚ_p}} in coordinates ({x | ρ(σ)·σ(x) = x}),
  `IsDeRhamStd ρ` = (finrank = n), the printed definition of "V de Rham"; `dualRep ρ σ = ρ(σ⁻¹)ᵀ`.
- LEAF `FontaineDRTannakian p`: de Rham reps (printed definition, on V) stable under (a) duals, (b) sub on the
  last b coordinates / quotient on the first a of a block lower-triangular ρ, (c) ⊕, (d) ⊗ (Kronecker);
  continuity of the inputs assumed. Fontaine Astérisque 223 Exp. II/III §1.5; Brinon–Conrad Thm 5.2.1,
  §6.3 (numbering UNVERIFIED).
- GLUE proved: `isDeRham_iff_std : IsDeRham ρ ↔ IsDeRhamStd (dualRep ρ)` (pkg-I4's Hom form of D_dR(V^∨)
  vs the printed tensor form, through coordinates), `isDeRham_conj` (clause (i), no leaf needed),
  `contRep_dualRep`, `dualRep_dualRep`, transposes of block/Kronecker matrices.
- PROOF `t23_all_of_fontaine : (∀ p, FontaineDRTannakian p) → ∀ p, T23_FontaineClosure p`.
  COMPILED 05:05, standard axioms. VERIFIED.

## H-22 `G0Galois.R14Det` (HodgeSplit.lean §8)
- Row copied verbatim (Leaves5.lean l.35303-35330: toRingEquivQ, cycQ, R14Det).
- PROVED `r14Det_of_wt : R14DetWt1 → R14DetWtGe2 → R14Det` (weight split; Shimura's k=2 not needed).
- LEAVES: `DSThm965` (Deligne via Diamond–Shurman Thm 9.6.5, k ≥ 2: ρ unramified outside ℓN, charpoly of
  arithmetic Frobenius = X² − a_p X + χ(p)p^{k−1}, coefficients extended to ℚ̄_ℓ by ιL∘ιC⁻¹; no
  semisimplicity), `DSThm966` (Deligne–Serre Thm 4.1 / DS Thm 9.6.6, k = 1: complex ρ, finite image,
  tr = a_p, det = χ(p) at arithmetic Frobenius). Numbering UNVERIFIED.
- GLUE (named, NOT proved): `Semisimplification2` (2-dim semisimplification keeps charpolys and unramified
  set), `DetFromFrobenius` (det from Frobenius values: Chebotarev + cyclotomic character mod N),
  `ArtinTransport` (DSThm966 → R14DetWt1: finite subgroup of GL₂(ℂ) realized over ℚ̄, then ιL; Maschke).
- PROVED `r14DetWtGe2_of_ds`, `r14Det_of_ds : DSThm965 → DSThm966 → Semisimplification2 →
  DetFromFrobenius → ArtinTransport → R14Det`. COMPILED 05:25, standard axioms. VERIFIED.
