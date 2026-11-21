---
article_id: af_45fff05ecc3aee55a906d96a
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves75.shimuraThm1Af
---

# Shimura's abelian variety attached to a newform

The *Shimura statement* is the following assertion. Let $f\in S_2(\Gamma_1(N))$ be a newform with
character $\chi$, $N\ge2$; let $X$, $P_0$ and $J$ be as in the [introduction](README.md), and $T_p$
($p$ prime) and $\langle d\rangle$ ($d\in(\mathbb Z/N)^\times$) Hecke operators on $J$ in the sense
there. Let $I_f$ be the set of endomorphisms $h(T_p,\langle d\rangle)$ of $J$, for $h$ a polynomial
with integer coefficients in noncommuting variables, one for each prime $p$ and each $d$, such that
$h(a_p(f),\chi(d))=0$; a homomorphism $\phi$ from $J$ *kills $I_fJ$* when $\phi\circ u=0$ for every
$u\in I_f$. For an abelian variety $A$ over $\mathbb Q$, a homomorphism $\nu:J\to A$ and a ring
homomorphism $\theta:K_f\to\operatorname{End}^0(A)$, consider the clauses: (i) $\nu$ is surjective
and has connected kernel, in the sense that whenever $\nu=\psi\circ\phi$ with $\phi:J\to B$ a
surjective homomorphism onto an abelian variety and $\psi:B\to A$ an isogeny, $\psi$ is an
isomorphism; (ii) for every prime $p$, $\nu\circ T_p=\theta(a_p(f))\circ\nu$, and for every prime
$p\nmid N$, $\nu\circ(T_p^2-p\langle p\rangle)=\theta(a_{p^2}(f))\circ\nu$, both in
$\operatorname{Hom}(J,A)\otimes\mathbb Q$, where $\nu\circ t=\theta(a)\circ\nu$ there means that for
some integer $m>0$, $m\,\theta(a)$ is an endomorphism $e$ of $A$ with $m(\nu\circ t)=e\circ\nu$;
(iii) $\dim A=[K_f:\mathbb Q]$. Then $K_f$ is a number field, and there is a triple $(A,\nu,\theta)$
with (i)–(iii) such that $\nu$ kills $I_fJ$ and every homomorphism from $J$ to an abelian variety
that kills $I_fJ$ factors uniquely through $\nu$; and for every triple $(A',\nu',\theta')$ with
(i)–(iii) there is an isomorphism $\psi:A\to A'$ over $\mathbb Q$ with $\psi\circ\nu=\nu'$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Shimura's Theorem 1, for a normalized eigenform of all
the $T_n$ on any group between $\Gamma_1(N)$ and $\Gamma_0(N)$, constructs the quotient $A=J/C$ with
$C=\ker\nu$, builds $C$ from the ideal of the Hecke ring annihilating $f$ intersected with
$\operatorname{End}(J)$, gives (i)–(iii) with $\nu\circ\xi_n=\theta(a_n)\circ\nu$ for every $n$, and
states that under (i) and (ii) the triple is unique up to isomorphism over $\mathbb Q$; an AI
reading of the print found these on pp. 525–527. Three steps are made on the spot: that $C$ is
$I_fJ$, through a saturation argument and the Hecke relations between Shimura's $\xi_n$ and the
$T_p$, $\langle d\rangle$; that (ii) at $n=p$ and $n=p^2$, with $\xi_{p^2}=T_p^2-p\langle p\rangle$,
gives (ii) for every $n$, so that the triples of the uniqueness clause are Shimura's; and that his
isomorphism is compatible with $\nu$. The uniqueness clause here compares only triples that also
satisfy (iii), which weakens the printed one. The statement takes $\Gamma=\Gamma_1(N)$ and newforms,
takes $T_p$ to be Shimura's $\xi_p$ through the identifications of the statement on Hecke operators,
and omits his clauses on the cotangent space and on the zeta function of $A$. Diamond and Shurman
define $A_f$ as $J/I_fJ$ over $\mathbb C$. A review of this statement is pending. It is a
hypothesis, not proved here.

## Depends on

None.

## Sources

- [Shimura abelian varieties](../../../sources/height-decomposition-locators.md#shimura-abelian-varieties)
