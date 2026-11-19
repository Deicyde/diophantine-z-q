---
declaration: theorem
origin: cited
---

# The genus bound before odd normalization (3.4)–(3.6)

Fix a negative odd fundamental discriminant $h_*$ with $|h_*|>4$, $L_*(h_*)\ne0$, in the same squareclasses
at $2N$ as the prepared positive filter containing $1$. Let $h$ be a known simple-zero parameter in that
filter, prime to the fixed support, and $k'$ a companion as in (3.3), with the primes of $h_*$ excluded. Let
$P^{\rm gen}_h$ be the unaveraged conductor-one genus sum over $\mathbb Q(\sqrt{hh_*})$ and
$P^{\rm rc}_{h,k'}$ the unaveraged ring-class sum of conductor $|h|$ over $\mathbb Q(\sqrt{k'})$, weighted by
$\chi_h$; write $j_{\rm gen}(h)$ and $j_{\rm rc}(h,k')$ for their index valuations in their native rank-one
lattices. Then
$$2j_{\rm rc}(h,k')-2j_{\rm gen}(h)=v_2L_*(hk')-v_2L_*(h_*)+\epsilon,\qquad|\epsilon|\le2,\tag{3.4}$$
up to the one fixed period convention; for each fixed $A$ and $\omega(k')\le A$,
$$2j_{\rm rc}(h,k')\ge4\omega(h)+s(h)+s(hk')-C_R(E,A);\tag{3.5}$$
and consequently
$$2j_{\rm gen}(h)\ge2\omega(h)+s(h)-C\tag{3.6}$$
with $C$ independent of $h$.

**Proof sketch.** Theorem 1.1 of Cai–Shu–Tian applies twice: every level prime splits, the conductors are
prime to $N$, fields with extra units are excluded, the parametrization is the same, the conductor factor is
$c\sqrt{|\operatorname{disc}K|}$ and the sums are unaveraged. The two Rankin products share the factor
$L(E^{(h)},s)$, so the ratio of the two heights is $L_*(hk')/L_*(h_*)$. Each rational free line has index at
most two in its native lattice (conjugation fixes the free class, and the norm makes twice the class
rational), which gives (3.4). The estimate (3.5) is the uniform lower bound (5.5) of Section 9 combined with
the central calibration (4.6) at the known nonzero point; it uses no odd normalization. Adding (3.3)–(3.5)
cancels $s(hk')$ and gives (3.6), with $C=C_R+C_E+2A+2-v_2L_*(h_*)$.

## Depends on

- [A bounded companion in the prepared filter (3.3)](rough-companion.md)

## Proof depends on

- [Uniform ring lower bound and height-one regularity (5.5)](../heegner-limits/uniform-lower-bound.md)
- [Central specialization and arithmetic calibration (4.5), (4.6)](../heegner-limits/central-calibration.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-genus-lower` (L2403–2458)

## Manuscript check

Checked by AI review. The deduction of (3.6) from (3.3)–(3.5) was checked by script, with the constant
above; it needs only $t_p\ge0$ where the proof of (3.5) invokes $\sum_{p\mid k}t_p\le2A$ (L5201). The
deduction of (3.5) from (5.5) and (4.6) was checked. The comparison (3.4) needs Theorem 1.1 of
Cai–Shu–Tian in a precise form: the point is the plain sum over the ring class group, the height is
normalized relative to $K$ and not to the ring class field, and the conductor and discriminant enter only
through $c\sqrt{|\operatorname{disc}K|}$, with $u=[\mathcal O_c^\times:\mathbb Z^\times]=1$ and $2^{\mu}=1$
since every prime of $N$ splits. This has not yet been checked against the print. Odd factors would not
matter, since $c=|h|$, $k'$ and $hh_*$ are odd; a factor whose $2$-adic valuation grows with $\omega(c)$, such
as $2^{\omega(c)}$, would shift (3.4) by a multiple of $\omega(h)$, and (3.4) is used both as a lower bound,
here and in (F.4), and as an upper bound for $j_{\rm rc}$ in the final family.
