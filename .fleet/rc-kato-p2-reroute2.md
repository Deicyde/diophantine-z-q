# Dyadic Kato reroute: corrected source

**Verdict: the conditional replacement route to (K15) is checked.**
The reading desk's check of Kato 1999, pp. 314-319, fixes three errors in
the earlier transcription: the full-open kernel has local conditions at
every prime dividing the base; condition (iii) requires purity; and the
printed torsion assertion is primewise. The unrevised citation of Kato
2004 at 2 still has the proof gap recorded in issue #168.

The new route compares the dyadic kernel on `C_j` with the full-open
kernel on `C_S`. It proves the comparison from the exact fragment of
(K16), derives weight −1 from the proved Hasse bound for the twisted
Euler polynomial, and derives global torsion separately from finite
generation and the two Iwasawa signs. The new Appendix E adapters keep
the original output types. The finite comparison uses the same
obligation as `AppEK1.FixedKatoFiniteComparison`. All seven new modules
compile; the audit of 28 declarations finds only the standard axioms
and no dependency on the old dyadic bound.

**Before integration:** supply the actual cohomology and coefficient
identifications, including the geometric odd support triangle, the
degree-one comparison, reciprocity and generic nonvanishing. The
construction after (K15) remains a separate input. The corrected print
is still a draft; registered leaves and frozen hypotheses are unchanged.

See the [report](../docs/research/rc-kato-p2-reroute2.md) and
[axiom audit](../scratch/rc-kato-p2-reroute2/axioms.txt).
