# Dyadic Kato reroute

**Source gap (issue #168).** The proof cited at tex 1884–1893 and
7206–7241 does not justify the application of Kato 2004, Theorem 13.4,
at coefficient prime two. In particular the field in the old fixed-space
argument is cyclotomic, while Kato 1999 §0.6(ii) requires a witness over
ℚᵃᵇ. The frozen implication itself takes Theorem 5.3 as a hypothesis.

**Verdict: conditional reroute checked.** The extended system on all
smoother-coprime multiples of `2Nd` has the required norm from Prop. 8.12
and the finite transfer laws. Its §0.7 class is the image of the retained
dyadic class, without a field-degree scalar. Serre's open image gives
the abelian-kernel fixed-space witness and cyclotomic absolute
irreducibility for the actual quadratic twist. The new Appendix E and
finite consumers give the existing output types. All eight modules pass
Lean. The audit covers 36 theorems with only the standard axioms and
finds no dependency on the old dyadic conclusion in the replacements.

**Before integration:** check the unverified 1999 draft against pp.
314–318 and construct the named full-open to retained cohomology
comparisons. Actual reciprocity, generic nonvanishing and the construction
after (K15) remain separate inputs. There is one new draft source and no
change in registered leaves or frozen hypotheses. See the
[report](../docs/research/rc-kato-p2-reroute.md) and
[axiom output](../scratch/rc-kato-p2-reroute/axioms.txt).
