---
article_id: af_85ec2598e01e79cfc3287e70
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.abscissa_val_even
---

# Parity of the abscissa on $y^2=x(x-\ell)(x+\ell)$

Let $p$ be a prime, $\ell\in\mathbb Q^\times$ with $v_p(\ell)$ even, and
$x,y\in\mathbb Q$ with $x\ne0$ and
$$y^2=x(x-\ell)(x+\ell).$$
Then $v_p(x)$ is even.

**Proof sketch.** If $v_p(x)=v_p(\ell)$ there is nothing to prove. Otherwise
$v_p(x-\ell)=v_p(x+\ell)=\min(v_p(x),v_p(\ell))$, by the equality case of the ultrametric
inequality, at every prime $p$; in particular both factors are nonzero, so the right
side is nonzero, $y\ne0$, and
$$2v_p(y)=v_p(x)+2\min\bigl(v_p(x),v_p(\ell)\bigr).$$
Hence $v_p(x)$ is even. (This is the manuscript's square-scaling step: after scaling $\ell$
to a unit, the cubic has valuation $v_p(x)$ if $v_p(x)>0$ and $3v_p(x)$ if $v_p(x)<0$.) The
manuscript's curve $y^2=x(x-\ell)(x+3\ell)$ needs $p\ne3$ at this step; the Route K curve needs
no condition on $p$.

## Depends on

None.

## Sources

- [One-sided obstruction](../../sources/multiplication-locators.md#one-sided-obstruction)
