---
article_id: af_8c6ac9f9d840c5a9366105e5
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.x_pointR_add_cT0, ZInQ.x_pointR_add_cTdelta, ZInQ.x_pointR_add_cTnegdelta
---

# The translates of $R$ by two-torsion

On $C:y^2=x^3-\delta^2x$ with $R=(1+s,2s)$:
$$x(R)=1+s,\quad x\bigl(R+(0,0)\bigr)=23-17s,\quad x\bigl(R+(\delta,0)\bigr)=2+4s,\quad
x\bigl(R+(-\delta,0)\bigr)=\frac{5-4s}{2}.$$
Each sum is computed by the chord rule with distinct abscissas. These are closed identities
in $K_0$: a finite computation.

**Proof sketch.** The chord slopes are $2s/(1+s)=4-2s$, $2s/(2s-2)=2+s$ and $2s/4=s/2$; then
$x_3=\lambda^2-x_1-x_2$ gives $(24-16s)-(1+s)=23-17s$, $(6+4s)-(1+s)-(3-s)=2+4s$ and
$\tfrac12-(1+s)+(3-s)=\tfrac52-2s$.

## Depends on

- [The certificate for the point $R$](../descent/point-r-certificate.md)

## Sources

- [Finite search](../../../sources/model-locators.md#finite-search)
