---
article_id: af_700260cec8870badbab91b60
declaration: def
origin: cited
statement: formalized
lean: ZInQ.K0, ZInQ.sqrt2, ZInQ.epsilon, ZInQ.delta, ZInQ.Zs
---

# The field $K_0=\mathbb Q(\sqrt2)$

Let $K_0=\mathbb Q(s)$ with $s^2=2$. Every element of $K_0$ is uniquely $u+vs$ with
$u,v\in\mathbb Q$, its *components*; addition is componentwise and
$$(a+bs)(c+es)=(ac+2be)+(ae+bc)s .$$
The *conjugate* of $z=u+vs$ is $\bar z=u-vs$, the *norm* is
$\operatorname N(z)=z\bar z=u^2-2v^2\in\mathbb Q$ and the *trace* is $\operatorname{Tr}(z)=2u$.
The two real embeddings are $\sigma_+(u+vs)=u+v\sqrt2$ and $\sigma_-(u+vs)=u-v\sqrt2$;
$\operatorname N(z)=\sigma_+(z)\sigma_-(z)$. An element is *totally positive* if both
embeddings are positive, and its *sign vector* is the pair of signs of
$\sigma_+(z),\sigma_-(z)$.

The subring $\mathbb Z[s]=\{u+vs:u,v\in\mathbb Z\}$ has fraction field $K_0$. Two fixed
elements recur throughout the chapter:
$$\epsilon=1+s,\qquad \delta=3-s .$$

The field is $\mathbb Q$ adjoined a square root of $2$; $2$ is not a rational square, so
$K_0$ is a field of degree two over $\mathbb Q$.

## Depends on

None.

## Sources

- [Model setup](../../../sources/model-locators.md#model-setup)
- [First descent image](../../../sources/model-locators.md#first-descent-image)
