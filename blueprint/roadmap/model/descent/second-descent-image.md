---
article_id: af_1c8151abc986bb3b1aedaf76
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.kummer_E'_trivial
---

# The second descent image is trivial

Let $E'=E_{4d^2}:y^2=x^3+4d^2x$ over $K_0$ and $\alpha'=\alpha_{4d^2}$ its Kummer map. Then
$\alpha'(Q)=1$ for every $Q\in E'(K_0)$.

**Proof sketch.** $\alpha'(O)=1$ and $\alpha'((0,0))=4d^2$ is a square. Let $Q=(x,y)$ with
$x\ne0$. *Total positivity.* In each real embedding $\sigma(y)^2=\sigma(x)(\sigma(x)^2+4\sigma(d)^2)$
with the second factor positive, so $\sigma(x)>0$; also $y\ne0$, since $x^2=-4d^2$ has no
solution in the real field $K_0$. *Even valuations.* Let $m=v_\pi(x)$. If $\pi$ is associate to
neither $s$ nor $d$, $v_\pi(4d^2)=0$ and, as for the first image, odd $m$ is impossible. At
$\pi=s$, $v_s(4d^2)=4$; the terms $x^3$ and $4d^2x$ have valuations $3m$ and $m+4$, equal only
for $m=2$, so for odd $m$ the valuation $2v_s(y)$ would be $\min(3m,m+4)$, odd. At $\pi=d$,
$v_d(4d^2)=2$; the valuations $3m$ and $m+2$ are equal only for $m=1$, so odd $m\ne1$ is
excluded as before. If $m=1$, write $x=dw$ with $v_d(w)=0$; then
$y^2=d^3w(w^2+4)$ forces $v_d(w^2+4)$ odd, in particular $w^2\equiv-4$ modulo $d$, so $(w/2)^2$
would be $-1$ in the residue field $\mathbb F_7$, which is impossible. *Conclusion.* By unique
factorization $x=uz^2$ with $u$ a unit; $u=x/z^2$ is totally positive, hence a square, so
$\alpha'(Q)=1$.

## Depends on

- [Two-isogenies and the Kummer map](kummer-map.md)
- [The generator curve $E$](../field/generator-curve.md)

## Proof depends on

- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](../field/integers-pid.md)
- [Units of $\mathbb Z[\sqrt2]$](../field/units.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../field/special-primes.md)

## Sources

- [Second descent image](../../../sources/model-locators.md#second-descent-image)
