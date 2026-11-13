---
article_id: af_6adb5a3fa0ba7845489fd6ca
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Selmer.CertifiedRankSel
---

# The certified rank hypothesis in Selmer form

The hypothesis CR₃^Sel is the following assertion. Let $d$ be a squarefree positive integer with
$d\equiv5\pmod8$. Suppose that the 2-Selmer group $\mathrm{Sel}_2(C_d)$ has exactly $8$ elements and
contains a pair $(a,b)$ with $|a|\equiv7\pmod8$. Then for every $(a',b')\in\mathrm{Sel}_2(C_d)$ the
2-covering $D_{a',b'}$ is soluble over $\mathbb Q$ (in its x-form).

Unlike CR₃, it mentions no Legendre symbols, configurations or linear system: those enter only
through Proposition 0, which is proved. In the literature's terms, by the Kummer-map lemma over
$\mathbb Q$ and the identification of the Kummer map with the connecting map of the complete
2-descent (Silverman X.1.4), the conclusion says that every Selmer class comes from a rational
point, that is $Ш(C_d)[2]=0$. Since $C_d(\mathbb Q)[2]$ has order $4$, the image of
$C_d(\mathbb Q)$ has dimension $2+\operatorname{rank}C_d(\mathbb Q)$, so when $\mathrm{Sel}_2(C_d)$ has
$8$ elements, $\operatorname{rank}C_d(\mathbb Q)\ge1$ gives the conclusion (with Mordell–Weil); the
converse is not formalized here. It rests on:

- for exactly the shape $d\equiv5$, $|a|\equiv7\pmod8$, Tian–Yuan–Zhang (Theorem 3.5 and the
  argument of the proof of Theorem 3.5(2), as completed by Proposition N), which gives that
  $L(C_d,s)$ vanishes to order one at $s=1$ (their hypothesis, an odd genus sum, follows from the
  premises by Corollary 4.4, Theorem 3.6 and Rédei's formula), and Gross–Zagier over an auxiliary
  imaginary quadratic field (Bump–Friedberg–Hoffstein), which gives
  $\operatorname{rank}C_d(\mathbb Q)\ge1$; then the image of $C_d(\mathbb Q)$ has dimension at
  least $3=\dim\mathrm{Sel}_2$, which forces $Ш(C_d)[2]=0$;
- as an alternative that is not needed, Kriz's 2-converse theorem (Theorem 10.13, a preprint whose publication status
  was not checked) for $C_d$ at $p=2$, whose standing assumption holds since $d\ge21$ (by Proposition 0
  the class $a$ is a signed divisor of $d$, so $d=|a|m$ with $m\equiv3\pmod8$), together with the
  corank lemma (Cassels–Tate: the pairing on $Ш/Ш_{\rm div}$ is nondegenerate and alternating, so
  $\dim(Ш/Ш_{\rm div})[2]$ is even, with no finiteness of $Ш$ assumed), giving rank one and
  $Ш(C_d)[2]=0$.

Neither rank theorem is formalized here, so CR₃^Sel is a hypothesis, not proved; the step
from positive rank to every Selmer class is a theorem
([RK9](../rank/two-descent/every-selmer-class.md)). CR₃^Sel implies CR₃ by Proposition 0, so the
main theorem holds with CR₃^Sel in place of CR₃. A sufficient condition in the terms of Smith's
matrices is the [row-5b hypothesis](../rank-5b/certified-rank-5b.md). With Mordell–Weil for $C_d$,
which is proved, CR₃^Sel also follows from its positive-rank form
[CR₃^Rk](../rank/certified-rank-rk.md).

## Depends on

- [The 2-Selmer group of a congruent number curve](selmer-group.md)

## Sources

- [The hypothesis in the literature's form](../../sources/selmer-locators.md#the-hypothesis-in-the-literatures-form)
- [Deep inputs of CR3Sel](../../sources/selmer-locators.md#deep-inputs-of-cr3sel)
- [The trust statement for CR3](../../sources/route-k-locators.md#the-trust-statement-for-cr3)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
