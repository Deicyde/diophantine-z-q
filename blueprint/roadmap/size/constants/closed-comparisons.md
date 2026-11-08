---
article_id: af_56d022ec8d070b320c36883c
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Size.closed_comparisons
---

# Closed numerical comparisons

The following inequalities between explicit natural numbers hold:

1. $433+22\cdot2^{4608}<2^{4613}$ and $4+1262628+16104\cdot2^{4608}<2^{4623}$, where
   $1262628=433\cdot2916$ and $16104=22\cdot732$;
2. $2+10\cdot2^{4613}<2^{4617}$;
3. $10^{12}<2^{40}$ and $2250+2^{9009}<2^{9010}$;
4. $4096\cdot85033<2^{29}$;
5. $(96\cdot10^{13})^{13}<2^{650}$ and $2210\cdot116064000000^2<2^{86}$;
6. $11243+2\cdot7950=27143$, $3\cdot3^4+6\cdot27143\cdot3^2+27143^2<2^{30}$,
   $2\,(3^6+5\cdot27143\cdot3^4+5\cdot27143^2\cdot3^2+27143^3)<2^{46}$ and
   $16\,(3^3+27143\cdot3)^2<2^{38}$;
7. $\max(6564,4640,123720,87483)<2^{17}$ and $65536\cdot1281<2^{27}$.

This is a finite computation. Every number involved has at most $9011$ binary digits; none of
the constants $D$, $T$, $H_{\rm cat}$, $N_s$, $M_0$, $c_*$, $\ell$ or $c_3$ occurs. These are the
closed comparisons used by the symbolic estimates of this chapter: (1) for $N_s$ and $\ell$,
(2) for $c_*$, (3) for $R=D$ and the upper bound on $D$, (4) for $C_{\rm cm}$, (5) for the
bound on $T$, (6) for the base cases of the division polynomials and (7) for the code heights.
The program literal is bounded in the compiler chapter, not here.

**Proof sketch.** Direct evaluation. For instance $4096\cdot85033=348295168<536870912=2^{29}$,
$65536\cdot1281=83951616<134217728=2^{27}$, and
$22\cdot2^{4608}+433<32\cdot2^{4608}=2^{4613}$ because $433<10\cdot2^{4608}$. Items 1 and 2
are those of the cutoff $2^{W^8}$; the manuscript's cutoff $2^{W^3}$ used the exponents
$2048$, $2053$, $2054$, $2059$ and $2063$ instead.

## Depends on

None.

## Sources

- [Proof of Proposition 12.1, catalogue](../../../sources/size-locators.md#proof-of-proposition-121-catalogue)
- [Proof of Proposition 12.1, cutoff](../../../sources/size-locators.md#proof-of-proposition-121-cutoff)
- [Section 12.1 norms and division polynomials](../../../sources/size-locators.md#section-121-norms-and-division-polynomials)
- [Section 12.1 constructor bounds](../../../sources/size-locators.md#section-121-constructor-bounds)
