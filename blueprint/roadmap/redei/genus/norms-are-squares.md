---
article_id: af_f8d08735ebb8c5676736f41b
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.isSquare_normZ_mod, ZInQ.RouteK.Redei.legBit_absNorm_span
---

# Norms are squares modulo the primes of $n$

Let $n\ge1$ be squarefree, $\mathcal O$ the ring of integers of $\mathbb Q(\sqrt{-n})$ and $q$ a
prime dividing $n$. For every $x\in\mathcal O$, the norm $N(x)$ is a square modulo $q$. Hence
$[N((x))/q]=0$ for every principal ideal $(x)$ of $\mathcal O$.

**Proof sketch.** As $n$ is squarefree and $q\mid n$, the ideal $\mathfrak p_q$ over $q$ is
ramified: $\mathfrak p_q^2=q\mathcal O$, so $N(\mathfrak p_q)=q$ and $\sigma\mathfrak p_q=\mathfrak p_q$.
So $x\equiv m\pmod{\mathfrak p_q}$ for an integer $m$, and $x-\sigma(x)\in\mathfrak p_q$. Then
$$N(x)-m^2=x\bigl(\sigma(x)-x\bigr)+(x-m)(x+m)\in\mathfrak p_q\cap\mathbb Z=q\mathbb Z.$$
The ideal norm of $(x)$ is $|N(x)|=N(x)$, since norms are nonnegative, so its residue bit is $0$.
No coordinates on $\mathcal O$ are needed.

## Depends on

- [Integers and norms of $\mathbb Q(\sqrt{-n})$](../field/integers-and-norms.md)
- [Residue bits](../../route-k/residue-bits.md)

## Proof depends on

- [The primes of the discriminant ramify](../field/ramified-prime-ideals.md)
- [Ramified primes divide the discriminant](../field/ramified-primes-divide.md)
- [Split, inert and ramified primes](../field/prime-trichotomy.md)
- [The conjugation of $\mathbb Q(\sqrt{-n})$](../field/conjugation.md)

## Sources

- [The chosen route](../../../sources/redei-locators.md#the-chosen-route)
- [Step 4: genus characters](../../../sources/redei-locators.md#step-4-genus-characters)
