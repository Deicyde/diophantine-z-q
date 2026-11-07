---
article_id: af_c0d526f1f4209b800feaa168
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Assembly.vS_star, ZInQ.Assembly.vS_trace_ge
---

# Valuation and trace at the prime $(s)$

Let $v_s$ be the valuation of $K_0$ at the prime $(s)$, normalized by $v_s(s)=1$ (so
$v_s(2)=2$), $\sigma$ the conjugation $s\mapsto-s$ and $\operatorname{Tr}x=x+\sigma x\in\mathbb Q$. Then:

1. $v_s(\sigma x)=v_s(x)$ for every $x\in K_0$;
2. if $k\in\mathbb Z$ and $v_s(x)\ge2k$, then $v_2(\operatorname{Tr}x)\ge k+1$.

At an odd prime $p$ the corresponding facts, with the bound $v_p(\operatorname{Tr}x)\ge k$ when
$v_{\mathfrak p}(x)\ge k$ at every prime $\mathfrak p$ above $p$, are those of
[the primes above $p$](../../multiplication/local/primes-above-p.md).

**Proof sketch.** (1) $\sigma$ is a ring automorphism of $\mathbb Z[s]$ and $\sigma(s)=-s$ is
associate to $s$. (2) Write $x=a+bs$ with $a,b\in\mathbb Q$. By the valuation formula at $(s)$,
$v_s(x)=\min(2v_2(a),2v_2(b)+1)\ge2k$ gives $v_2(a)\ge k$, so $v_2(\operatorname{Tr}x)=v_2(2a)\ge k+1$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Sources

- [Lemma 11.1](../../../sources/assembly-locators.md#lemma-111)
- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
