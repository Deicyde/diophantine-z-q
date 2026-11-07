---
article_id: af_e723f99aa1a5e5b7a132dda6
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Mult.rational_height_bounds
---

# Sum and quotient bounds for rational heights

For a rational number $x=a/b$ in lowest terms with $b>0$ let $h(x)=\log\max(|a|,b)$. For all
$x_1,x_2,x_3,x,y\in\mathbb Q$ with $y\ne0$:
$$h(x_1+x_2+x_3)\le h(x_1)+h(x_2)+h(x_3)+\log3,\qquad h(x/y)\le h(x)+h(y),$$
and $h(-x)=h(x)\ge0$, $h(1/y)=h(y)$.

**Proof sketch.** Write $x_i=a_i/b_i$ in lowest terms. The sum is
$\bigl(\sum_ia_i\prod_{j\ne i}b_j\bigr)/(b_1b_2b_3)$; after reduction its numerator has absolute
value at most $3\prod_i\max(|a_i|,b_i)$ and its denominator at most
$\prod_ib_i\le\prod_i\max(|a_i|,b_i)$. For the quotient, $x/y=(a d)/(b c)$ for $y=c/d$, and
reduction only decreases numerator and denominator, whose absolute values are at most
$\max(|a|,b)\max(|c|,d)$. Inversion swaps numerator and denominator up to sign.

## Depends on

None.

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
