---
article_id: af_009cb01e3f509bfbfcdf0e67
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.k0_identities, ZInQ.K0.totallyPositive_iff, ZInQ.k0_signs
---

# Explicit identities in $K_0$

With $s^2=2$, $\epsilon=1+s$, $\delta=3-s$ and $d=75-53s$, the following closed statements hold
in $K_0$ and in $\mathbb Z$:

1. $d^2=11243-7950s$ and $\operatorname N(d)=75^2-2\cdot53^2=7$;
2. $\epsilon(s-1)=1$, $\epsilon^2=3+2s$, $\epsilon^4=17+12s$, $\epsilon^6=99+70s$ and
   $\operatorname N(\epsilon)=-1$;
3. $d\,\epsilon^4=\delta$, that is $(75-53s)(17+12s)=3-s$; $\delta^2=11-6s$; $\operatorname N(\delta)=7$;
   $\operatorname N(s)=-2$;
4. $75>0$ and $75^2>2\cdot53^2$; $3>0$ and $3^2>2\cdot1^2$; $1^2<2\cdot1^2$; $2\le2^2$;
5. $2^6\cdot7^4=392^2=153664$, $7^2<392$ and $676=26^2$.

An element $u+vs$ with $u,v\in\mathbb Q$ is totally positive exactly when $u>0$ and
$u^2>2v^2$. So item 4 says that $d$ and $\delta$ are totally positive, that $\epsilon$ has sign
vector $(+,-)$ (as $\sigma_-(\epsilon)=1-\sqrt2<0<\sigma_+(\epsilon)$), and that
$\sigma_\pm(\delta)=3\mp\sqrt2$ lies in $[1,5]$ (both bounds amount to $\sqrt2\le2$).

All items are equalities of explicit elements of $K_0$ (two rational components each) or
comparisons of explicit integers: a finite computation.

**Proof sketch.** Expand with $s^2=2$ and compare components; evaluate the integers. For the
positivity criterion: $u\pm v\sqrt2>0$ for both signs is $u>|v|\sqrt2$, i.e. $u>0$ and
$u^2>2v^2$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](quadratic-field.md)

## Sources

- [Model setup](../../../sources/model-locators.md#model-setup)
- [Class number and units](../../../sources/model-locators.md#class-number-and-units)
- [First descent image](../../../sources/model-locators.md#first-descent-image)
- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
