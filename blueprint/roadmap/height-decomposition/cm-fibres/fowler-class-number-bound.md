---
article_id: af_f7d75f9670b327ccf5726c0c
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves72.fowlerProp27PrintCanonical
---

# Fowler's bound for discriminants of bounded class number

The *Fowler statement* is the following assertion. Let $\Delta<0$ be an integer with $\Delta\equiv0$
or $1\pmod4$, and let $h(\Delta)$ be the class number of the imaginary quadratic order of
discriminant $\Delta$: the order of the Picard group of the order $\mathbb Z[\omega]$,
$\omega^2=\lfloor\Delta/4\rfloor+(\Delta\bmod4)\,\omega$, whose discriminant is $\Delta$. Then for
every integer $n\ge1$ with $h(\Delta)\le n$,
$$\sqrt{|\Delta|}\le2n^2\exp\bigl(21000\,n^2\bigr).$$

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
This is Fowler's Proposition 2.7 as printed: the print takes $h(\Delta)$ to be the class number of
the imaginary quadratic order of discriminant $\Delta$, which it calls unique. Lean proves that
uniqueness, up to ring isomorphism, and that every order of an imaginary quadratic field with
discriminant $\Delta$ has class number $h(\Delta)$, so the statement gives the form the height
argument uses: $\sqrt{|\Delta_R|}\le2n^2\exp(21000n^2)$ for every order $R$ with
$\#\operatorname{Pic}(R)\le n$. The manuscript cites the proposition and applies it at $n=D$. A
reviewer and a two-lens re-check rated it published against the printed page; no reading by a person
is recorded. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Fowler Proposition 2.7](../../../sources/height-decomposition-locators.md#fowler-proposition-27)
