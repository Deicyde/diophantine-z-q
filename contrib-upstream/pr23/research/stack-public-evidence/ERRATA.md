# Errata (additive)

This note changes no file. `research/detector-cube-reuse/references/precision51_PROOF.md`,
SHA-256 `e6a825c3b85a9c56a6a2678ad0fa411ecedec53a005a0464efb45677f056054c`,
is a verbatim copy of the fork's `research/higher-detector-precision/PROOF.md`
at `bc51100fd3ada82df0dac55d6f1d235219430c74`, as recorded in
`references/ORIGIN.json`. Its hash is bound there, so it is left as it is.
No proof, FINDINGS.json, EXPECTED.json, acceptance record or review record
has been edited.

## Reading of the recurrence for `G12` (lines 10–11)

The text says:

> `G12(w)=sum(a_j w^j,j=0..12)`, with `a0=1`, `a1=-2/5` and
> `a_j/a_(j-1)=(4j-5)/(4j+1)`.

**Read the ratio for j >= 2 only.** The value `a1 = -2/5` is given
separately. At j = 1 the ratio formula would give `a1/a0 = -1/5`, which
contradicts that value.

This changes no conclusion. Under the intended reading, the reduced
denominator of `a13` is `5^2*7*17*29*37*41*53`, as the proof states at
line 26. Under that reading `a13 = -54756974/6936596275` in lowest terms.
If the ratio were also applied at j = 1, `a13` would only be halved. The
reduced numerator 54756974 is even, so halving gives
`-27378487/6936596275`, which is still in lowest terms, and the reduced
denominator does not change. Therefore `v_p(a13) >= -1` holds at every
admitted prime under either reading.
`check_evidence.py` (`errata arithmetic`) verifies both values with exact
fractions.

Carlos Toledo raised this as a wording note, not as an objection, in his
non-author review of #8 to #16. He reported it among his checks of #13's
retained order-47 argument.
