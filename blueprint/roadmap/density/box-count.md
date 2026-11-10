---
article_id: af_cafc48b64ed84b1228a8d762
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.GaussSieve.abs_card_box_dvd_sub_le, ZInQ.Density.GaussSieve.box, ZInQ.Density.GaussSieve.gaussFZ, ZInQ.Density.GaussSieve.abs_card_Ico_cast_eq_sub_le
---

# Counting a box with a divisibility condition

Let $\ell,b$ be integers, $F(U,V)=(\ell U)^2+(b+\ell V)^2$, $d\ge1$, and let $\rho(d)$ be the number of
solutions of $F\equiv0\pmod d$ in $(\mathbb Z/d)^2$. For a box $\mathcal B=[a_1,a_1+M_1)\times[a_2,a_2+M_2)$ of
integer points,
$$\Bigl|\#\{(U,V)\in\mathcal B: d\mid F(U,V)\}-\rho(d)\frac{M_1M_2}{d^2}\Bigr|\le\rho(d)\,(M_1+M_2+1).$$

**Proof sketch.** An interval of $M$ consecutive integers has $M/d+\theta$ elements in each residue
class modulo $d$, with $|\theta|\le1$. For each of the $\rho(d)$ residue pairs the box contains
$(M_1/d+\theta_1)(M_2/d+\theta_2)$ points of the pair, which differs from $M_1M_2/d^2$ by at most
$M_1+M_2+1$ (as $d\ge1$); sum over the pairs.

## Depends on

None.

## Sources

- [The sieve](../../sources/density-locators.md#the-sieve)
