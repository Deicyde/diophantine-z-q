---
article_id: af_5243a58af240a78f881bfed7
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Size.E0sub, ZInQ.Size.E1sub, ZInQ.Size.redK, ZInQ.Size.reductionHom, ZInQ.Size.ker_reductionHom, ZInQ.Size.E0_eq_top_of_good, ZInQ.Size.zsmul_addOrderOf_mem_E1
---

# Reduction on the nonsingular part

Let $\mathfrak p$ be a nonzero prime of $\mathbb Z[s]$ with $2\notin\mathfrak p$, $k=\mathbb Z[s]/\mathfrak p$
its (finite, odd characteristic) residue field, $\mathcal O_{\mathfrak p}=\mathbb Z[s]_{\mathfrak p}\subset K_0$
the local ring and $\rho:\mathcal O_{\mathfrak p}\to k$ the residue map. Let $A\in\mathbb Z[s]$,
$W:y^2=x^3+Ax$ over $K_0$ and $\widetilde W:y^2=x^3+\rho(A)x$ over $k$. Let
$\widetilde W_{\rm ns}(k)$ be the group of nonsingular points of $\widetilde W$ over $k$
together with $O$, under the chord-and-tangent law. Put
$$W_1(\mathfrak p)=\{O\}\cup\{(x,y)\in W(K_0):x\notin\mathcal O_{\mathfrak p}\},$$
$$W_0(\mathfrak p)=W_1(\mathfrak p)\cup\{(x,y)\in W(K_0):x\in\mathcal O_{\mathfrak p},\ (\rho(x),\rho(y))\text{ is a nonsingular point of }\widetilde W\}.$$
(If $x\in\mathcal O_{\mathfrak p}$ then $y\in\mathcal O_{\mathfrak p}$, since $y^2=x^3+Ax$.) Define
$\operatorname{red}:W_0(\mathfrak p)\to\widetilde W_{\rm ns}(k)$ by $\operatorname{red}(Q)=O$ for
$Q\in W_1(\mathfrak p)$ and $\operatorname{red}(x,y)=(\rho(x),\rho(y))$ otherwise. Then:

1. $W_0(\mathfrak p)$ is a subgroup of $W(K_0)$ and $\operatorname{red}$ is a group
   homomorphism with kernel $W_1(\mathfrak p)$;
2. if $\rho(A)\ne0$, then $\widetilde W$ is nonsingular and $W_0(\mathfrak p)=W(K_0)$.

Consequently, if $Q\in W_0(\mathfrak p)$ and $n\ge1$ is the order of $\operatorname{red}(Q)$ in
the finite group $\widetilde W_{\rm ns}(k)$, then $[n]Q\in W_1(\mathfrak p)$, and so
$[mn]Q\in W_1(\mathfrak p)$ for every integer $m$.

**Proof sketch.** This is Silverman, Proposition VII.2.1, applied after embedding $K_0$
in its completion at $\mathfrak p$ (the local ring $\mathcal O_{\mathfrak p}$ is the
intersection of $K_0$ with the completed valuation ring, and the residue fields agree). The
model is integral at $\mathfrak p$, and the proof of VII.2.1 uses only integrality: the
group law is given by the chord-and-tangent construction, a line through points of
$W_0(\mathfrak p)$ reduces to the line through their reductions, and the third intersection
point reduces accordingly; points with $x\notin\mathcal O_{\mathfrak p}$ reduce to $O$. For
(2), the discriminant of $y^2=x^3+ax$ is $-64a^3$, nonzero in odd characteristic when
$a\ne0$; then every point with integral coordinates has nonsingular reduction. The final
statement follows from (1) since $W_1(\mathfrak p)$ is a subgroup.

The manuscript cites VII.2.1 for the nonsingular reduction group at the bad place and uses
the same homomorphism at the good places. The model chapter's reduction statement for split
primes of good reduction is the special case of (1) with residue degree one.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Proof depends on

- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../../multiplication/local/primes-above-p.md)

## Informally uses

- [Reduction is injective on prime-to-$p$ torsion](../../model/descent/reduction-torsion.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
- [Silverman](../../../sources/size-locators.md#silverman)
