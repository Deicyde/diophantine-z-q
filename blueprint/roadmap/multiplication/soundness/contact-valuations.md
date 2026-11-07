---
article_id: af_ffcc22aaa06007eced4e6bf0
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.contact_valuations
---

# Valuations of the normalization at an odd contact prime

Let $t\in\mathbb Q\setminus(\mathcal C\cup\{1\})$, $\eta\in\{1,-1\}$ and $q\in\mathbb Q$, and put
$R_0=\eta F(t)/(t-1)^8$, $a=1-R_0q^2$ and $R=\ell_0^2a^2R_0$ with $a\ne0$. Let $p\notin S_b$ be
a prime and $c\in\mathcal C$ with $k=v_p(t-c)$ positive and odd. Then:

1. $v_p(t-c')=0$ for every $c'\in\mathcal C\setminus\{c\}$ and $v_p(t-1)=0$; hence
   $v_p(R_0)=v_p(F(t))=k$;
2. $r=v_p(R)$ is odd and $r\le k$.

The manuscript records only that the factor valuations below are minima of zero and an odd
integer; the case $v_p(a)<0$, where $r=3k+4v_p(q)<k$ and $r$ may be negative, is part of the
statement.

**Proof sketch.** Since $p\notin S_b$, $p>324$ and $v_p(\ell_0)=0$. As $v_p(t-c)>0$, $t$ is
$p$-integral and $t\equiv c\pmod p$; for $c'\ne c$, $t-c'\equiv c-c'\not\equiv0$ because
$0<|c-c'|\le60<p$, and $t-1\equiv c-1\not\equiv0$ because $0<|c-1|\le61<p$. This gives (1).
Then $v_p(R_0q^2)=k+2v_p(q)$ is odd, hence nonzero (if $q=0$, $a=1$). If it is positive,
$v_p(a)=0$; if it is negative, $v_p(a)=k+2v_p(q)<0$. So $v_p(a)\le0$ and
$r=2v_p(a)+k$ is odd and at most $k$.

## Depends on

- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)

## Proof depends on

- [Properties of the multiplication constants](../certificate/constants-properties.md)

## Sources

- [Local congruence](../../../sources/multiplication-locators.md#local-congruence)
- [Slope predicate](../../../sources/multiplication-locators.md#slope-predicate)
