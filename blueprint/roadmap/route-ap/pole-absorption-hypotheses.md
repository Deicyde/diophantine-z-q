---
article_id: af_6b92c04eb95e037e454b5251
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.Mult.PoleAbsorbHyp, ZInQ.Mult.apContactNum
---

# The hypotheses of Lemma P

Let $\ell$ be a prime and $t\in\mathbb Q$, written $t=u/v$ in lowest terms with $v>0$. Then $t$
*satisfies the hypotheses of Lemma P at $\ell$* if

1. $e=v_\ell(v)\ge1$, that is, $t$ has a pole at $\ell$;
2. $e\ge3$ if $\ell=2$;
3. none of the seven numbers $u-cv$, $c\in\mathcal C\cup\{1\}$, is divisible by $\ell$.

The *contact numerator* of $(u,v)$ is $F(u,v)=\prod_{c\in\mathcal C}(u-cv)$, so that
$F(u/v)=F(u,v)/v^6$.

The research note also asks for $F(t)>0$; that condition only fixes the sign $\eta=1$ of the
slope predicate, and it is kept in field 2′ of the slope conditions rather than here.

## Depends on

- [Prime sets and clearing exponents of the multiplication certificate](../multiplication/certificate/constants.md)

## Sources

- [Lemma P](../../sources/route-ap-locators.md#lemma-p)
