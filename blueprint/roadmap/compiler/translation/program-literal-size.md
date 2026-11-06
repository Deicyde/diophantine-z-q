---
article_id: af_4a8e044aefac1d6ca7c31346
declaration: theorem
origin: bridged
---

# Size of the program literal

The wrapper $W(\Pi_{\rm prec})$ of the precision machine has $m\le2^{20}$ instructions, and every
register index and every target of its instructions is below $2^{20}$. Consequently the base
$2^w$ chosen by the encoding has $w\le20$, and the program literal satisfies
$$5\le c_3<2^{\,20(4\cdot2^{20}+1)+1}=2^{83886101}<2^{2^{27}} .$$

The first sentence is a closed decidable statement about the constructed instruction list
of $W(\Pi_{\rm prec})$: its length and the maximum of its register indices and targets. It is
checked on the list, never on $c_3$, whose digits are not computed. For comparison, the
manuscript's literal has $m=146\,780$ instructions, all indices below $2^{18}$, $w=18$ and
$3\,181\,317$ decimal digits. This bound is what the size chapter needs from the compiler: the
literal $c_3$ is one of the fixed integer constants of the specification, and Section 12
requires every literal constant to be at most $T$.

**Proof sketch.** Finite check for $m$ and the indices. Then $w$ is the least integer with
$2^w>2$ and $2^w$ greater than every index, so $2^w\le2^{20}$. By the bounds on codes in the
decoding lemma, $c_3=\operatorname{code}(W(\Pi_{\rm prec}))<2^{w(4m+1)+1}\le2^{20(4\cdot2^{20}+1)+1}$,
and $c_3\ge5$ because the first instruction of the wrapper is not $\mathrm{halt}$. Finally
$20(4\cdot2^{20}+1)+1=83886101<134217728=2^{27}$.

## Depends on

- [The wrapper and the program literal](machine/wrapper.md)
- [The universal program numbering](machine/program-numbering.md)

## Proof depends on

- [Decoding a program code](machine/program-numbering-decode.md)

## Sources

- [Section 12 literal constants](../../../sources/compiler-translation-locators.md#section-12-literal-constants)
- [Section 10.3 specialization](../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
