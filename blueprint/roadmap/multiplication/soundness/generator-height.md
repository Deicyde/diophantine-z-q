---
article_id: af_f0a470175447ecc8285c0636
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.generator_height, ZInQ.Mult.canonHeightE
---

# The canonical height of multiples of $P_0$

Let $\theta:E(K_0)\to C(K_0)$, $(x,y)\mapsto(\epsilon^4x,\epsilon^6y)$, be the change of variables to
$C:y^2=x^3-(3-s)^2x$, and put $\widehat h(Q)=\widehat h_C(\theta(Q))$ for $Q\in E(K_0)$, where
$\widehat h_C$ is the canonical height on $C(K_0)$ (normalized so that
$2\widehat h_C=\lim4^{-m}h_x\circ[2^m]$). Then:

1. $\widehat h([n]P_0)=n^2\,\widehat h(P_0)$ for every $n\in\mathbb Z$;
2. $2\widehat h(P_0)\ge\log41-\tfrac13\log392>1$;
3. for every $Q\in E(K_0)\setminus\{O\}$, $2\widehat h(Q)\le h(\epsilon^4x(Q))+\tfrac13\log676$,
   and $\widehat h(O)=0$.

The manuscript uses $2\widehat h(P_0)>1$ without proof; it follows from the height of $2R$.

**Proof sketch.** $\theta$ is a group isomorphism with $\theta(P_0)=[2]R$, so
$\theta([n]P_0)=[n]([2]R)$ and (1) is the quadratic property of $\widehat h_C$. For (2), the basic
comparison $h_x(T)\le2\widehat h_C(T)+\tfrac13\log392$ at $T=[2]R$, with $h_x([2]R)=\log41$, gives
$2\widehat h_C([2]R)\ge\log41-\tfrac13\log392$, which exceeds $1$ by the explicit height
constants. (3) is the other basic comparison $2\widehat h_C(T)\le h_x(T)+\tfrac13\log676$ at
$T=\theta(Q)$, whose abscissa is $\epsilon^4x(Q)$.

## Depends on

- [The change of variables to $C$](../../model/descent/coordinate-change.md)
- [The canonical height on $C(K_0)$](../../model/heights/canonical-height.md)
- [The point $P_0$](../../model/field/generator-point.md)

## Proof depends on

- [The canonical height is quadratic](../../model/heights/canonical-height-quadratic.md)
- [Basic properties of the canonical height](../../model/heights/canonical-height-bounds.md)
- [The height of $2R$](../../model/heights/height-of-2r.md)
- [The certificate for the point $R$](../../model/descent/point-r-certificate.md)
- [Explicit height constants](height-constants.md)

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
- [Generator height](../../../sources/multiplication-locators.md#generator-height)
