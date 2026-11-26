---
article_id: af_45ac59bf4014bb2c454ed7b4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Boolean.missingAddressNode, ZInQ.Contrib.CloudB3RC53.MissingAddressNode, ZInQ.Manuscript.RC.Boolean.coefficient_transfer, ZInQ.Manuscript.RC.Boolean.difference_estimate, ZInQ.Manuscript.RC.Boolean.missingAddressNode_gt
---

# Proposition 9.9: finite coefficient transfer

Assume, as hypotheses of the theorem, the inequalities $M>c_{\det}$, $M>B+2c_{\det}$ and
$b>(L_T+2)(2^M-1)$ of [(5.10)](equation-5-10-choice.md), and coefficient data over $\mathbb F_2^b$ with
the outputs of [Proposition 9.8](proposition-9-8-common-denominator.md) at the precision $M$: the
identity $f_x\widetilde u_x=d_x$ at every character, with bounded denominators for $\widetilde u_x$; the
pole bound $L_T$ modulo $2^M$; and a regular base, $f_0\in\Lambda$ with $v_2f_0(0)=c\le c_{\det}$.

Then some nonzero address $x$ has
$$v_2\bigl(\widetilde u_x(0)-\widetilde u_0(0)\bigr)\ge M-2c>B,\tag{5.11}$$
where the second inequality follows from $M>B+2c_{\det}$ and $c\le c_{\det}$.

The manuscript goes on: if $L'(E/K,1)=0$, [Lemma 8.11](../section-8/lemma-8-11-base-zero.md) makes
$\widetilde u_0(0)=0$, against the bound $v_2\widetilde u_x(0)\le B$ at the nonzero addresses; since
$L(E^{(k)},1)\ne0$ and $L(E/K,s)=L(E,s)L(E^{(k)},s)$, $E$ has analytic rank one. In Lean that conclusion
is the last step of [the reduction](../reduction.md).

`missingAddressNode` uses the pole bound only at the one precision $M$ and gets
$\widetilde u_x\in\Lambda[1/2]$ from the bounded denominators; it states the first inequality of (5.11) in
norm form, $|\widetilde u_x(0)-\widetilde u_0(0)|_2\le2^{2c-M}$, and leaves $M-2c>B$ to
`missingAddressNode_gt`, as arithmetic. `coefficient_transfer` states (5.11), both inequalities, from
(5.9) at every precision, regularity and (5.10).

The per-address step is `difference_estimate`. Assume, as hypotheses of that theorem, at the base and at
one address $x$: the identities $f_0\widetilde u_0=d_0$ (in degree zero) and $f_x\widetilde u_x=d_x$ as
convergent convolutions; $f_0\in\Lambda$ with $f_0(0)\ne0$ of valuation $c<M$; $\widetilde u_x\in\Lambda[1/2]$;
every negative coefficient of $f_x$ divisible by $2^M$; and the constant coefficients of $f_x$ and $d_x$
congruent modulo $2^M$ to those of $f_0$ and $d_0$. Then it gives the first inequality of (5.11) in norm
form. The proof of this proposition supplies these hypotheses at the missing address.

The reduction of Theorem 5.3 takes this statement from the theorem `missingAddressNode`, which uses
`difference_estimate`; its last step compares $M-2c$ with $B$ directly, without `missingAddressNode_gt`.

**Proof sketch.** For a coefficient of an element of $\mathscr O[G]$, the bit of index $j\ge1$ of its sign
values has Boolean degree at most $2^{j-1}$, so $q$ congruences modulo $2^M$ have total Boolean degree at
most $q(2^{M-1}-1)$. For the $L_T(M)+2$ tested coefficients (those of $f$ from $-L_T(M)$ to $0$, and the
constant one of $d$), (5.10) makes this less than $b$. The product of the complementary indicators then
sums to zero over the cube, so the solution set, which contains $0$ and has even size, contains a
nonzero address. There integrality of $d_0$ and $d_x$ gives $v_2\widetilde u\ge-c$ at both addresses.
Subtracting the constant terms,
$F_x(\widetilde u_x(0)-\widetilde u_0(0))=([t^0]d_x-[t^0]d_0)-(F_x-F_0)\widetilde u_0(0)-E_x$, where $F$
denotes the constant coefficient of $f$ and $E_x$ collects the products with the negative coefficients of
$f_x$. Every term on the right has valuation at least $M-c$, and $v_2F_x=c$, which gives (5.11).

## Depends on

- [Proposition 9.8: a common denominator for the corrected coordinate](proposition-9-8-common-denominator.md)
- [(5.10): the choice of the precision and the address dimension](equation-5-10-choice.md)

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
