---
article_id: af_a57ed2a7c0584ec5d3e159b0
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.pointR, ZInQ.theta_symm_two_smul_pointR
---

# The certificate for the point $R$

In $K_0$, with $\delta=3-s$:

1. $(2s)^2=(1+s)^3-\delta^2(1+s)$, so $R=(1+s,2s)\in C(K_0)$, and $2s\ne0$;
2. the tangent slope at $R$ is $\lambda=\frac{3(1+s)^2-\delta^2}{2\cdot2s}=\frac{12-s}{4}$, and
   $$[2]R=\Bigl(\lambda^2-2(1+s),\ \lambda\bigl((1+s)-x(2R)\bigr)-2s\Bigr)
   =\Bigl(\frac{57-28s}{8},\ \frac{-660+417s}{32}\Bigr);$$
3. $\epsilon^{-4}\cdot\frac{57-28s}{8}=\frac{1641-1160s}{8}$ and
   $\epsilon^{-6}\cdot\frac{-660+417s}{32}=\frac{-123720+87483s}{32}$, that is
   $\theta^{-1}([2]R)=P_0$.

All three items are closed identities between explicit elements of $K_0$: a finite
computation.

**Proof sketch.** Expand with $s^2=2$: $(1+s)^3=7+5s$, $\delta^2=11-6s$,
$\delta^2(1+s)=-1+5s$, so the right side of (1) is $8=(2s)^2$. For (2),
$3(1+s)^2-\delta^2=9+6s-11+6s=-2+12s$ and $(-2+12s)/(4s)=(12-s)/4$; then expand. For (3),
multiply by $\epsilon^4=17+12s$ and $\epsilon^6=99+70s$ and compare components.

## Depends on

- [The change of variables to $C$](coordinate-change.md)
- [The point $P_0$](../field/generator-point.md)

## Sources

- [First descent image](../../../sources/model-locators.md#first-descent-image)
- [Height comparison](../../../sources/model-locators.md#height-comparison)
- [Transfer to the generator](../../../sources/model-locators.md#transfer-to-the-generator)
