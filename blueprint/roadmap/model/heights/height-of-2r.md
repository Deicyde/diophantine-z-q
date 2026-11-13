---
article_id: af_50d450496f55534d7141e180
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.hx_two_R
---

# The height of $2R$

$h_x([2]R)=h\bigl(\tfrac{57-28s}{8}\bigr)=\log41$.

The proof reduces to three closed integer facts, a finite computation:
$$57^2-2\cdot28^2=41^2\ (=1681),\qquad 49^2>2\cdot28^2\ (2401>1568),\qquad 57\text{ is odd}.$$

**Proof sketch.** By the certificate for $R$, $x([2]R)=a/b$ with $a=57-28s$ and $b=8=s^6$. The
only prime dividing $b$ is $s$, and $s\nmid a$ because $57$ is odd, so $a,b$ are coprime. Both
embeddings of $a$ exceed $8$: $57+28\sqrt2>8$ trivially, and $57-28\sqrt2>8$ because
$49>28\sqrt2$, i.e. $49^2>2\cdot28^2$. By the height of a fraction,
$h=\tfrac12\log(\sigma_+(a)\sigma_-(a))=\tfrac12\log\operatorname N(a)=\tfrac12\log41^2$.

## Depends on

- [The $x$-height on $C(K_0)$](x-height.md)
- [The certificate for the point $R$](../descent/point-r-certificate.md)

## Proof depends on

- [The height of a fraction in $\mathbb Z[\sqrt2]$](x-height-formula.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../field/special-primes.md)

## Sources

- [Height comparison](../../../sources/model-locators.md#height-comparison)
