---
article_id: af_7121d7e331db6c27d70c3ca0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.generator_certificate, ZInQ.carrierD_eq_zmultiples, ZInQ.indexEquivCarrier, ZInQ.iota_injective
---

# The generator certificate

The point $P_0$ has infinite order and
$$2E(K_0)=\mathbb ZP_0 .$$
Consequently $n\mapsto[n]P_0$ is an isomorphism $\mathbb Z\to2E(K_0)=D$, the carrier $D$ is
torsion-free, and $n\mapsto\iota(n)$ is injective.

This is Proposition 3.1. The manuscript assumes the Mordell–Weil theorem to pass from the
descent index and the torsion bound to rank one; here Mordell–Weil is itself proved from the
descent, so the statement has no hypothesis. That $P_0$ has infinite order already follows from
the torsion theorem.

**Proof sketch.** Work on $C$ through the isomorphism $\theta$. By the rank-one theorem,
$C(K_0)=\mathbb ZS\oplus C(K_0)[2]$ with $S$ of infinite order; write $R=[m]S+T$ with
$T\in C(K_0)[2]$. Then $m$ is odd, in particular $m\ne0$. Suppose $|m|\ge3$. Then
$h_x(S)<\log9$, so by the search box $x(S)$ lies in the candidate set of the finite search,
and $f(x(S))=y(S)^2$ is a square; hence $x(S)$ is one of the seven survivors. The survivors
$0,\pm\delta$ are abscissas of two-torsion points, excluded because $S$ has infinite order.
The other four are the abscissas of $R+T'$ for $T'\in C(K_0)[2]$, so $S=\pm(R+T')$ for some
$T'$ (equal abscissas force equal or opposite points), and the basic properties give
$\widehat h(S)=\widehat h(R)$. But $\widehat h(R)=\widehat h([m]S)=m^2\widehat h(S)=m^2\widehat h(R)$ with
$m^2\ge9$ and $\widehat h(R)>0$, a contradiction. So $m=\pm1$, $C(K_0)=\mathbb ZR\oplus C(K_0)[2]$
and $2C(K_0)=\mathbb Z\,[2]R$, with $[2]R$ of infinite order. Applying $\theta^{-1}$, which sends
$[2]R$ to $P_0$ by the certificate for $R$, gives $2E(K_0)=\mathbb ZP_0$ with $P_0$ of infinite
order. Injectivity of $\iota$ follows from injectivity of codes.

## Depends on

- [The point $P_0$](field/generator-point.md)
- [Point codes](point-codes.md)

## Proof depends on

- [Mordell-Weil for $E/K_0$ from the descent](descent/mordell-weil-from-descent.md)
- [$E(K_0)$ has rank one](descent/rank-one.md)
- [The free index of $R$ is odd](descent/odd-free-index.md)
- [A multiple of a small point](heights/small-height-bound.md)
- [The search box for small heights](heights/search-box.md)
- [The finite search for small points on $C$](heights/small-height-search.md)
- [The translates of $R$ by two-torsion](heights/r-torsion-translates.md)
- [Basic properties of the canonical height](heights/canonical-height-bounds.md)
- [The canonical height is quadratic](heights/canonical-height-quadratic.md)
- [The certificate for the point $R$](descent/point-r-certificate.md)
- [The change of variables to $C$](descent/coordinate-change.md)
- [The torsion of $E(K_0)$ is the full two-torsion](descent/torsion.md)
- [Elementary properties of codes](field/point-code-properties.md)

## Sources

- [Generator certificate statement](../../sources/model-locators.md#generator-certificate-statement)
- [Finite search](../../sources/model-locators.md#finite-search)
- [Transfer to the generator](../../sources/model-locators.md#transfer-to-the-generator)
