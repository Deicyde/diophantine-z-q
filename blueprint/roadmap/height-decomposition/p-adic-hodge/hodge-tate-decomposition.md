---
article_id: af_fa507498f724129acce4d644
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves40.hodgeTateDecompExists
---

# The Hodge–Tate decomposition of an abelian variety

The *Hodge–Tate statement* is the following assertion. Let $A$ be an abelian variety over a finite
extension $F$ of $\mathbb Q_p$, and $V_p(A)$ its rational Tate module. Then there are integers
$a,b\ge0$ and a $G_F$-equivariant $\mathbb C_p$-linear isomorphism
$$\mathbb C_p\otimes_{\mathbb Q_p}V_p(A)\;\cong\;\mathbb C_p(1)^a\oplus\mathbb C_p^b,$$
where $G_F$ acts on the left by $\sigma\otimes\rho(\sigma)$ and on $\mathbb C_p(1)$ through the
cyclotomic character.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
The printed decomposition is $(\mathbb C_p(1)\otimes_F t_A)\oplus(\mathbb C_p\otimes_F t_{A'}^{*})$,
with $t_A$ the tangent space at the origin and $A'$ the dual; the statement chooses bases of the two
spaces and leaves their dimensions unnamed. That $a=b=\dim A$ is proved here, from the Weil pairing;
that proof rests on the two statements of this chapter about the
[Picard scheme](../abelian-varieties/picard-scheme-exists.md). The statement has not been read
against the source. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Hodge-Tate decomposition](../../../sources/height-decomposition-locators.md#hodge-tate-decomposition)
