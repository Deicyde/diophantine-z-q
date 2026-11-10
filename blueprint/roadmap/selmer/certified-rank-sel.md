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
$8$ elements the conclusion is equivalent to $\operatorname{rank}C_d(\mathbb Q)\ge1$. It rests on
either of:

- Kriz's 2-converse theorem (Theorem 10.13, an unrefereed preprint) for $C_d$ at $p=2$, whose
  standing assumption holds since $d\ge21$ (by Proposition 0 the class $a$ is a signed divisor of
  $d$, so $d=|a|m$ with $m\equiv3\pmod8$), together with the corank lemma (Poonen–Stoll: the
  Cassels–Tate pairing makes $\dim Ш[2]$ even when $Ш$ is finite), giving rank one and
  $Ш(C_d)[2]=0$;
- or, for exactly the shape $d\equiv5$, $|a|\equiv7\pmod8$, Tian–Yuan–Zhang (Theorem 3.5(2), with
  its proof), which gives that $L(C_d,s)$ vanishes to order one at $s=1$, and
  Gross–Zagier–Kolyvagin, which give rank one and $Ш(C_d)$ finite; then $\dim\mathrm{Sel}_2=3=2+1$
  forces $Ш(C_d)[2]=0$.

None of these is formalized here: CR₃^Sel is a hypothesis, not proved. It implies CR₃ by
Proposition 0, so the main theorem holds with CR₃^Sel in place of CR₃. A sufficient condition in
the terms of Smith's matrices is the [row-5b hypothesis](../rank-5b/certified-rank-5b.md).

## Depends on

- [The 2-Selmer group of a congruent number curve](selmer-group.md)

## Sources

- [The hypothesis in the literature's form](../../sources/selmer-locators.md#the-hypothesis-in-the-literatures-form)
- [Deep inputs of CR3Sel](../../sources/selmer-locators.md#deep-inputs-of-cr3sel)
