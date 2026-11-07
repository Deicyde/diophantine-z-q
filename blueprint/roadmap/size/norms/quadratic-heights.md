---
article_id: af_1489ec543a565d87e0f613ea
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.QRep, ZInQ.Size.QRep.exists_add, ZInQ.Size.QRep.exists_sub, ZInQ.Size.QRep.exists_mul, ZInQ.Size.QRep.exists_two_mul, ZInQ.Size.QRep.exists_div, ZInQ.Size.QRep.coord_bounds
---

# Sizes under quadratic-field operations

Say that an integer triple $(a,b,c)$ with $c\ne0$ represents $u=(a+bs)/c\in K_0$ and has
size $\max(|a|,|b|,|c|)$. Let $H\ge2$, and let $u,u'\in K_0$ be represented by triples of size
at most $H$. Then:

1. $u+u'$, $u-u'$, $uu'$ and $2u$ are represented by triples of size at most $3H^4$;
2. if $u'\ne0$, then $u/u'$ is represented by a triple of size at most $3H^4$;
3. if $(a,b,c)$ represents $u=u_0+u_1s$ ($u_0,u_1\in\mathbb Q$) with size at most $H$, then
   $u_0=a/c$ and $u_1=b/c$, and their reduced numerators have absolute value at most $H$ and
   their positive reduced denominators are at most $H$.

**Proof sketch.** With $u=(a+bs)/c$ and $u'=(a'+b's)/c'$:
$u\pm u'=\bigl((ac'\pm a'c)+(bc'\pm b'c)s\bigr)/(cc')$ has size at most $2H^2$;
$uu'=\bigl((aa'+2bb')+(ab'+a'b)s\bigr)/(cc')$ has size at most $3H^2$; $2u=(2a+2bs)/c$ has size
at most $2H$. For the quotient multiply by the conjugate:
$$\frac uu'=\frac{c'\bigl((aa'-2bb')+(a'b-ab')s\bigr)}{c\,(a'^2-2b'^2)},$$
where $a'^2-2b'^2\ne0$ because $a'+b's\ne0$ and $\sqrt2$ is irrational; the size is at most
$3H^3$. All these are at most $3H^4$. For (3), reducing a fraction does not increase the
absolute values of its numerator and denominator.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Sources

- [Section 12.1 constructor bounds](../../../sources/size-locators.md#section-121-constructor-bounds)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
