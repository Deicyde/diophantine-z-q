---
article_id: af_a9153e37829b9e4aeba1b220
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Mult.S_ht, ZInQ.Mult.catalogue, ZInQ.Mult.S_b, ZInQ.Mult.S_mul, ZInQ.Mult.Bp, ZInQ.Mult.Cp, ZInQ.Mult.Dp, ZInQ.Mult.Ep, ZInQ.Mult.contactPoly, ZInQ.Mult.IsOddContactPrime, ZInQ.Mult.prec
---

# Prime sets and clearing exponents of the multiplication certificate

The constants $M_0$, $c_*=4M_0$, $\ell_0$ (the constant $\ell=12P_s^{2916}H_{\rm cat}^{732}$),
$R=\max(D,H_{\max},c_*,10^{12})$, $A_{\rm ht}=2\cdot10^{13}\max(1,C_{\rm cm},Q^{17})$ with
$Q=R^{RE_0}$, and $T=(48A_{\rm ht})^{13}$ are the prescribed fixed constants. In terms of
them define:

- $S_{\rm ht}=\{p\text{ prime}:p\le324\}$; $\mathcal H$ the fixed prime catalogue (the first
  twenty-two primes greater than $324$ in each unit class modulo $W=4P_s$);
  $S_b=S_{\rm ht}\cup\mathcal H$; and
  $$S_{\rm mul}=S_{\rm ht}\cup\mathcal H\cup\{p\text{ prime}:p\mid c_*\};$$
- for $p\in S_b$: $B_p=4$ if $p\in S_{\rm ht}$ and $B_p=1$ if $p\in\mathcal H$;
  $C_p=14B_p$, $D_p=51C_p$ and $E_p=52C_p+v_p(12)+4$;
- the contact set $\mathcal C=\{0,-15,-20,-24,-30,-60\}$ and
  $F(t)=t(t+15)(t+20)(t+24)(t+30)(t+60)=\prod_{c\in\mathcal C}(t-c)$;
- for $t\in\mathbb Q$, a prime $p$ is an *odd contact prime* of $t$ if $v_p(t-c)$ is positive
  and odd for some $c\in\mathcal C$; for a finite set $S$ of primes, $M_S(t)$ is the product of
  the odd contact primes of $t$ outside $S$, as in the six-contact estimate;
- the test precisions $k_j=1$ for $1\le j\le8$ and $k_j=25$ for $9\le j\le12$.

These are definitions; none of the constants is evaluated. The manuscript writes
$S_{\rm mul}=S_{\rm ht}\cup\mathcal H\cup\operatorname{supp}(c_*)$ and uses $S_b$ for the old
primes at which the fixed normalization $\ell_0$ clears denominators.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)
- [The prime catalogue](../../syntax/constants/prime-catalogue.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)

## Sources

- [Contact prime sets](../../../sources/multiplication-locators.md#contact-prime-sets)
- [Fixed local clearing](../../../sources/multiplication-locators.md#fixed-local-clearing)
- [Fixed constants](../../../sources/multiplication-locators.md#fixed-constants)
- [Slope predicate](../../../sources/multiplication-locators.md#slope-predicate)
