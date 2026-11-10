---
article_id: af_d6427210834a14db2c75d746
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.lemmaP_one, ZInQ.Mult.lemmaP_two, ZInQ.Mult.lemmaP_two_ball, ZInQ.Mult.lemmaP_two_rat, ZInQ.Mult.exists_sqrt_apContactNum, ZInQ.Mult.apContactNum_dvd, ZInQ.Mult.contactQuot_apContactNum, ZInQ.Mult.PoleAbsorbHyp.not_dvd, ZInQ.Mult.not_dvd_apContactNum, ZInQ.Mult.norm_intCast_eq_one_of_not_dvd, ZInQ.Mult.PoleAbsorbHyp.num_sub_den_ne_zero, ZInQ.Mult.eq_num_div_den, ZInQ.Mult.exists_int_div_pow_near, ZInQ.Mult.norm_one_sub_le_of_near
---

# Lemma P: a pole at an old prime is absorbed by the parameter $q$

Let $\ell$ be a prime and let $t=u/v$ satisfy the hypotheses of Lemma P at $\ell$, with
$e=v_\ell(v)$, and put $R_0=F(t)/(t-1)^8$. Then:

1. $v_\ell(R_0)=2e$, $v_\ell(t-1)=-e$, and $R_0$ is a square in $\mathbb Q_\ell$;
2. for every integer $N$ the set of $x\in\mathbb Q_\ell$ with $|1-R_0x^2|_\ell\le\ell^{-N}$ is
   non-empty and open in $\mathbb Q_\ell$; more precisely there are $m\in\mathbb Z$ and
   $k,M\in\mathbb N$ such that every rational $q$ with $|q-m/\ell^k|_\ell\le\ell^{-M}$ satisfies
   $|1-R_0q^2|_\ell\le\ell^{-N}$, that is $v_\ell(1-R_0q^2)\ge N$ (or $1-R_0q^2=0$). In particular
   such a rational $q$ exists.

**Proof sketch.** (1) With $F(u,v)$ the contact numerator,
$R_0=F(u,v)\,v^2/(u-v)^8$. The numbers $u-cv$ and $u-v$ are $\ell$-units, so
$v_\ell(R_0)=2e$ and $v_\ell(t-1)=v_\ell(u-v)-v_\ell(v)=-e$. Since $v\mid F(u,v)-u^6$, the unit
$X=F(u,v)$ is congruent to $u^6$ modulo $\ell^e$; Hensel's lemma for $Y^2-X$ at $Y=u^3$ applies
because $|u^6-X|_\ell\le\ell^{-e}<|2u^3|_\ell^2$ (for $\ell=2$ this needs $e\ge3$). So $X=y^2$ in
$\mathbb Z_\ell$, and $R_0=z^2$ with $z=vy/(u-v)^4$. (2) Put $w=z^{-1}$, so that $R_0w^2=1$. If $|x-w|_\ell\le|w|_\ell\min(1,\ell^{-N})$, then
$1-R_0x^2=R_0(w-x)(w+x)$ has absolute value at most $\ell^{-N}$, by the ultrametric inequality.
The set is the preimage of a closed ball, which is open in $\mathbb Q_\ell$; and the rationals
$m/\ell^k$ are dense in $\mathbb Q_\ell$, which gives the rational ball.

The note's hypothesis $F(t)>0$ is not needed for these statements; it only fixes $\eta=1$.

## Depends on

- [The hypotheses of Lemma P](pole-absorption-hypotheses.md)
- [The slope predicate](../multiplication/certificate/slope-predicate.md)

## Sources

- [Lemma P](../../sources/route-ap-locators.md#lemma-p)
