# hdec-elementary: fleet report

**Verdict.** Theorem 4.1 (H = `ZInQ.SixContactMin`) follows from **12 research-level leaves**,
5 groups of textbook foundations (mostly formalized already in Tau Ceti or Stacks), and 23 glue
steps that hold every argument of Glazer's and of the repository (descent, conductor bound,
Lemma PR, NoCM, bookkeeping). Note: `docs/research/hdec-elementary.md`. Lean draft:
`scratch/hdec-elementary/Leaves.lean`, which compiles with one `sorry` (the E/F arithmetic glue).
The F1 algebra `j = 3779136·I₁₀²/I₄⁵` and the step `JHeightBound → SixContactMin` are proved
there, with standard axioms.

**Leaves.** L1 canonical model / moduli of `Y₃` (Shimura, Deligne, Kottwitz); L2 branch data and
Igusa vector (Baba–Granath, Lin–Yang); L3 Shimura reciprocity at CM points (González–Rotger);
L4 Grothendieck's monodromy theorem; L5 Faltings 1983 (semisimplicity, Tate); L6 GL₂-type
abelian varieties over `ℚ` are modular (Khare–Wintenberger + Ribet); L7 `cond(A_f) = N^{dim}`
(Carayol + Shimura + Li); L8 Javanpeykar; L9 Gaudron–Rémond Thm 1.4; L10 Faltings Lemma 5;
L11 Bost; L12 Pazuki Cor. 1.3(2) with Thomae.

**Route changes.** (i) Route K replaces Pan + p-adic Hodge theory + eigenform Galois
representations (N5 C2-C10) by L6 + L7 and two NEW lemmas. This removes all of p-adic Hodge
theory from the definitions. (ii) Good reduction is used in Galois form, so Néron models,
Raynaud and NOS drop out of the leaf list. (iii) Theta constants are replaced by the Thomae
point (roots of the sextic). F1 becomes algebra on the QM locus
`[I₂:I₄:I₆:I₁₀] = [96(j+1):576j:4608j(5j+4):4096j³]`.

**Statable now.** None of L1-L12 faithfully. Statable and stated with genuine definitions:
Igusa–Clebsch invariants, the QM locus, the Thomae point, absolute Weil heights, and Igusa's
1960 theorem (a foundation). L8-L12 are stated over a placeholder signature, which is not
faithful until the objects are real (the fake-model problem of wk-h §4.3).

**Biggest missing definition.** The stable Faltings height (needed by L8-L12). Next come the
Shimura curve `Y₃` as a PEL moduli scheme with its CM points (L1-L3), then `J₁(N)` over `ℚ` and
Tate modules.

**Most serious risk.** Route K's two new glue lemmas (GL₂-type factor of `Res_{L'/ℚ} A`;
Glazer's break bound transplanted to `Ind`) are unreviewed, and the locator of the
Khare–Wintenberger GL₂-type corollary is UNVERIFIED. Have both reviewed before anyone
formalizes route K. N5's route P remains the fallback, with about 8 more leaves.
