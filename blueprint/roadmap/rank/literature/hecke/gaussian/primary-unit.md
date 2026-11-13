---
article_id: af_6199850ac174ea8ef03b093e
declaration: def
origin: background
statement: formalized
lean: ZInQ.Contrib.HeckeFE.unitOf, ZInQ.Contrib.HeckeFE.unitG, ZInQ.Contrib.HeckeFE.unitOf_eq_unitG, ZInQ.Contrib.HeckeFE.unitG_mul, ZInQ.Contrib.HeckeFE.unitOf_eq_zero_of_even, ZInQ.Contrib.HeckeAll.unitG_eq_zero_of_two_mul, ZInQ.Contrib.GaussFE.unitOf_primary
---

# The primary unit of a Gaussian integer modulo 4

For $(a,b)\in(\mathbb Z/4)^2$ the *primary unit* $u(a,b)\in\{0,\pm1,\pm i\}$ is given by the table
$$u(a,b)=\begin{cases}1&(a,b)\in\{(1,0),(3,2)\},\\-1&(a,b)\in\{(3,0),(1,2)\},\\
i&(a,b)\in\{(0,3),(2,1)\},\\-i&(a,b)\in\{(0,1),(2,3)\},\\0&\text{otherwise.}\end{cases}$$
The same table with values in $\mathbb Z[i]$ defines $u_G(a,b)$. For a Gaussian integer
$\alpha=x+yi$, $u(\alpha)$ means $u(x\bmod4,\,y\bmod4)$. For each $\alpha$ with $x+y$ odd, the table
lists the unit $u$ with $u\alpha\equiv1\pmod{2+2i}$; this description is motivation only, and only
the facts below are used.

1. $u(a,b)$ is the image of $u_G(a,b)$ in $\mathbb C$.
2. $u_G$ is multiplicative for the Gaussian product modulo $4$: for all $a,b,c,e\in\mathbb Z/4$,
   $u_G(ac-be,\,ae+bc)=u_G(a,b)\,u_G(c,e)$.
3. If the least residues of $a$ and $b$ have even sum, then $u(a,b)=0$.
4. If $2(a^2+b^2)=0$ in $\mathbb Z/4$, then $u_G(a,b)=0$.
5. If $x\equiv1$ and $y\equiv0\pmod4$, or $x\equiv3$ and $y\equiv2\pmod4$, then $u(x+yi)=1$.

**Proof sketch.** Each statement is a finite check over the residues modulo $4$ ($256$ cases
for (2)).

## Depends on

None.

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
