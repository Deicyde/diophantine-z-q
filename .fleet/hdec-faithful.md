# hdec-faithful: fleet report

**Verdict.** Glazer's proof of Theorem 4.1, in the instance `SixContactMin`, decomposes cleanly
along N5 (with the repository's adopted replacements: Lemma PR, NoCM, the determinant argument)
into literature leaves and glue (`docs/research/hdec-faithful.md`). It does not decompose into
about ten theorems. Done faithfully, there are **40 leaves: 21 research-level theorems from 18
sources and 19 textbook theorems**, in **eight packages** (P1 the discriminant-6 Shimura curve,
P2 reduction theory, P3 classical abelian varieties, P4 arithmetic of ℚ, P5 Faltings, P6 p-adic
Hodge theory and modularity, P7 modular curves, P8 Arakelov heights). The packages are the honest
unit of "about ten". The glue is G0-G20. The new arguments are Glazer's scalar descent, the
representation and twist, and the uniform conductor bound, plus the repository's Lemma PR and
NoCM. G20 (back to `u`) is already proved in Lean. Every glue step cites its leaves; none hides
a deep theorem.

**Statable in Lean now (VERIFIED: `scratch/hdec-faithful/Leaves.lean` compiles with
`lake env lean`).** Eight statements are written over genuine Mathlib definitions plus cheap new
ones (`G_ℚ`, inertia and Frobenius via valuation subrings of `ℚ̄`, continuous
`GL_n(ℚ̄_ℓ)`-representations, cusp forms on `Γ₁(N)` with nebentypus, eigenforms via the Hecke
recursion of their q-coefficients):
- Skolem–Noether (L14);
- the Hasse principle for central simple ℚ-algebras (L15a);
- Kronecker–Weber (L17);
- Chebotarev in density form (L18);
- Brauer–Nesbitt (L19);
- existence of eigenform Galois representations (L27a);
- Deligne–Serre finiteness in weight one (L27b);
- twisting of eigenforms (L28a).

The other 35 statements are named placeholders (`def … : Prop := sorry`, no content) with exact
docstrings. `sixContactMin_of_leaves` takes all 43 as hypotheses and is proved from
`jHeightBound_of_leaves` (`sorry`) through the existing Lean proof of G20. Two small glue facts
are proved, with standard axioms only.

**Biggest missing definition.** The Faltings height. Five leaves need it (Javanpeykar,
Gaudron–Rémond, Faltings' height lemma, Bost, Pazuki), and it is very large. Next in size is
the moduli scheme `Y₃` of QM abelian surfaces of discriminant 6, with its canonical model (five
leaves). The medium definition that unlocks the most is abelian varieties with ℓ-adic Tate
modules and Galois action, which unlocks Faltings, Néron–Ogg–Shafarevich, Raynaud and Mumford's
theorems.

**Most serious risk.** A leaf stated stronger than published. Pan's conclusion, "comes from a
cuspidal eigenform up to twist", is undefined in his introduction. The note fixes a trace reading
that every reading in the literature implies. Several leaves are in a consequence form whose
derivation needs Chebotarev and Brauer–Nesbitt. L1 is assembled from several statements of
Shimura 1967 and Deligne 1971. The glue itself (Glazer's new arguments, Lemma PR, NoCM) has only
model reviews. Almost all theorem numbers are UNVERIFIED in the journals; the ones to check first
are Pan's JAMS numbering, Baba–Granath and Lin–Yang's journal numbering, and Carayol at `p | N`.
