---
article_id: af_095c27de41c3a3a60de425ba
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves76.afCharpolyDS965
---

# Frobenius on the Tate module of Shimura's abelian variety

The *Frobenius statement on $A_f$* is the following assertion. Let $f\in S_2(\Gamma_1(N))$ be a
newform with character $\chi$, $N\ge2$; let $X$, $P_0$ and $J$ be as in the
[introduction](README.md), $T_p$ ($p$ prime) and $\langle d\rangle$ ($d\in(\mathbb Z/N)^\times$)
Hecke operators on $J$ in the sense there, and $I_f$ as in the statement on
[Shimura's abelian variety](shimura-abelian-varieties.md). Let $A$ be an abelian variety over
$\mathbb Q$ with a surjective homomorphism $\pi:J\to A$ that kills $I_fJ$ and through which every
homomorphism from $J$ to an abelian variety killing $I_fJ$ factors uniquely, and let
$\theta:K_f\to\operatorname{End}^0(A)$ be a ring homomorphism such that, for every prime $p$,
$\theta(a_p(f))$ is an endomorphism $e$ of $A$ with $\pi\circ T_p=e\circ\pi$, and, for every $d$,
$\chi(d)$ lies in $K_f$ and $\theta(\chi(d))$ is an endomorphism $e$ of $A$ with
$\pi\circ\langle d\rangle=e\circ\pi$. Suppose that $K_f$ is a number field. Let $\ell$ be a prime,
$\lambda$ a place of $K_f$ above $\ell$ and
$V_\lambda=K_{f,\lambda}\otimes_{\mathbb Q_\ell\otimes K_f}V_\ell(A)$, where $K_f$ acts on
$V_\ell(A)$ through $\theta$, and suppose that $V_\lambda$ is finite-dimensional over
$K_{f,\lambda}$. Then for every prime $p\nmid N\ell$, $\chi(p)$ lies in $K_f$ and every arithmetic
Frobenius at $p$ acts on $V_\lambda$ with characteristic polynomial $x^2-a_p(f)x+\chi(p)\,p$ over
$K_{f,\lambda}$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Diamond and Shurman's Theorem 9.6.5 asserts that there
is a representation $\rho_{f,\lambda}$ in which Frobenius has this characteristic polynomial, and a
paragraph after it, on the same page, identifies $\rho_{f,\lambda}$ for $k=2$ with the construction
of their Section 9.5 on $V_\ell(A_f)$, which is $V_\lambda$. The statement asks for the polynomial
on every $(A,\pi,\theta)$ with these properties of $A_f$, for newforms with $N\ge2$, and drops
irreducibility and unramifiedness; that $K_f$ is a number field and that $V_\lambda$ is
finite-dimensional are the print's presuppositions. A review rates it a consequence: the theorem is
an existence statement, identified with $V_\lambda$ only in the text after it, and that the given
Hecke operators and $I_f$ are Diamond and Shurman's rests on statements about the complex points and
the Abel–Jacobi map of $X_1(N)$ that are not proved here. That $(A,\pi)$ is unique up to unique
isomorphism, and $\theta$ determined by it, is proved here. A human reader has checked the theorem
at $k=2$, the paragraph after it and Section 9.5 in a print copy of the corrected fourth printing
(2016). Diamond and Shurman state the characteristic polynomial for $k=2$ without proof or citation,
and Section 9.5 proves only that Frobenius satisfies it. It is a hypothesis, not proved here.

## Depends on

- [Shimura's abelian variety attached to a newform](shimura-abelian-varieties.md)

## Sources

- [Diamond-Shurman 9.6.5 on Af](../../../sources/height-decomposition-locators.md#diamond-shurman-965-on-af)
