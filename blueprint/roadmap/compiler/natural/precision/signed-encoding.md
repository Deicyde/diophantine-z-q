---
article_id: af_c1cd30b92807dac845926c6f
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Precision.enc, ZInQ.Compiler.Precision.dec, ZInQ.Compiler.Precision.decode5
---

# The signed encoding of integers

The *signed encoding* $\operatorname{enc}:\mathbb Z\to\mathbb N$ and its *decoding*
$\operatorname{dec}:\mathbb N\to\mathbb Z$ are
$$\operatorname{enc}(n)=\begin{cases}2n,&n\ge0,\\-2n-1,&n<0,\end{cases}\qquad
\operatorname{dec}(c)=\begin{cases}c/2,&c\text{ even},\\-(c+1)/2,&c\text{ odd}.\end{cases}$$
A tuple $c=(c_0,c_1,c_2,c_3,c_4)\in\mathbb N^5$ of precision inputs decodes, in this fixed
order, to $(n,\kappa,a,l,j)=(\operatorname{dec}c_0,\dots,\operatorname{dec}c_4)\in\mathbb Z^5$.

This is a definition. The order $(n,\kappa,a,l,j)$ is the order in which the ordinary-value
relation links its five signed codes to the precision inputs.

## Depends on

None.

## Sources

- [Section 10 signed encoding](../../../../sources/compiler-natural-locators.md#section-10-signed-encoding)
