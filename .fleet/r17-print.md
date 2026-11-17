# r17-print (2026-11-16)

**Result:** `r17 : LadicCond.CarayolR17'` is proved in Lean from a new printed-form leaf `CarayolPrinted.CarayolThmA` (Carayol 1986 Théorème (A), F = ℚ, weight 2, packaged form), together with the existing bundle field `eigenformCoeffFieldFinite`. No new glue Prop.

The leaf is stated over Tau Ceti's printed `Newform N 2` and the printed coefficient field `K_{f,λ}` (Mathlib `adicCompletion`). It asserts that there is a continuous, absolutely irreducible (Burnside form) `ρ : G_ℚ → GL₂(K_{f,λ})` with:
- arithmetic-Frobenius trace `a_p` at `p ∤ Nℓ`;
- Serre–Tate conductor exponent `v_p(N)` at every `p ≠ ℓ`.

Every dictionary step is proved:
- `IsNewform` = printed newform (newform-dict);
- the place `λ_τ` and the extension `τ̂` (DSCoeffExt);
- new: `condExp` is invariant under extension of scalars;
- new: absolute irreducibility implies semisimplicity after extension;
- Brauer–Nesbitt + Chebotarev and `condExp` invariant under isomorphism (r17-bypass's CarayolLevel).

**Compiles (VERIFIED):**
- `ZInQKernel/Contrib/OneProof/CarayolPrinted.lean`, with no warnings in the file and standard axioms;
- `#discharges`: `DISCHARGES [OpenResearchLeaves28.r17] by CarayolPrinted.carayolR17'_of_printed`, still assuming `[CarayolThmA, EigenformCoeffFieldFinite]`, standard axioms;
- autofold dry run: strict 16/21 → 17/20; the generated `sixContactMin_of_open39` compiles with standard axioms.

**Count:** −1 GLUE with the leaf flagged `unread` (kind published), as the kit prescribes for new printed leaves. Reading risk, disclosed in the flag and the report: Carayol's own wording is local–global compatibility with π_p. The conductor clause needs Casselman 1973, and absolute irreducibility is Ribet 1977. The packaged form is believed printed (DDT 1997 Thm 3.1, Carayol §0.8), but nobody has read it (UNVERIFIED). If a check finds it unprinted, the leaf becomes `pending reading` and the effect is 0.

**Remains:**
- a statement check of the leaf;
- the fold, which imports CarayolLevel and NewformDict through the contribution.

Report: docs/research/r17-print.md.
