---
article_id: af_fea335fde9760f46198e77d4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.pair_norm_estimates
---

# The weighted pair norm

For $u=a+bs$ and $u'=a'+b's$ in $S[s]$, $S=\mathbb Z[X_i:i\in I]$, and $c\in\mathbb Z$:

1. $\|u+u'\|\le\|u\|+\|u'\|$, $\|u-u'\|\le\|u\|+\|u'\|$ and $\|cu\|=|c|\,\|u\|$;
2. $\|uu'\|\le\|u\|\,\|u'\|$, hence $\|u^k\|\le\|u\|^k$;
3. $\deg(u+u')\le\max(\deg u,\deg u')$ and $\deg(uu')\le\deg u+\deg u'$;
4. $\|a\|_1\le\|u\|$ and $\|b\|_1\le\|u\|$;
5. for integers $e,f$, the constant $e+fs$ has norm $|e|+2|f|$ and degree $0$, and the
   variable pair $X_i+X_js$ ($i\ne j$) has norm $3$ and degree $1$.

**Proof sketch.** (2): $uu'=(aa'+2bb')+(ab'+a'b)s$, so by the elementary estimates
$\|uu'\|\le\|a\|\|a'\|+2\|b\|\|b'\|+2\|a\|\|b'\|+2\|a'\|\|b\|\le(\|a\|+2\|b\|)(\|a'\|+2\|b'\|)$. The rest is
immediate from the scalar estimates.

The manuscript states that both norms are submultiplicative; the companion proof adds
subadditivity under the field operations.

## Depends on

- [Coefficient norms and degrees](l1-norm.md)

## Proof depends on

- [Elementary estimates for the coefficient norm](l1-norm-estimates.md)

## Sources

- [Section 12.1 norms and division polynomials](../../../sources/size-locators.md#section-121-norms-and-division-polynomials)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
