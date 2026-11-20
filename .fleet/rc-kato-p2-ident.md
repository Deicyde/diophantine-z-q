# Dyadic Kato identifications

**Scoped stop.** Both real eigenspaces of the genuine rational Tate twist
have dimension one. The new constituent constructor fills the negative
sign field used by the corrected Kodai draft. The existing Appendix E
and scalar consumers, including the fixed and curve versions, can use
that constructor without a separate sign argument. No new LEAF or GLUE
assumption was added; the registry was untouched.

The [report](../docs/research/rc-kato-p2-ident.md) records the existing
gap in the manuscript's application of Kato 2004 at two. No new source
error was established. In the generic reciprocity calculation, the
character dependent smoothers and the nonquadratic deck convention still
need to be matched to the source.

Both new Lean modules compile. The [axioms audit](../scratch/rc-kato-p2-ident/axioms.txt)
covers the constructor and all four theorems with only standard axioms.
The [sizing log](../scratch/rc-kato-p2-ident/log.md) gives the exact
remaining cuts.

The integral étale `j_*` and full-open towers, the geometric odd cone,
the degree-one comparison, reciprocity and equivariant character
specialization are still open. The separate Appendix E construction
after (K15) also remains conditional. Closing these gaps requires new
arithmetic comparison work beyond `FixedKatoFiniteComparison`, so issue
#168 remains open.
