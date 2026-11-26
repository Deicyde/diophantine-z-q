---
article_id: af_6db59bd7b65d9889031f009f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.PoleRC.crm_of_restrictedConverse_proved, ZInQ.Manuscript.PoleRC.CRM
---

# CR_M from Theorem 5.3, Lemma 5.4 and Lemma 5.5

$\mathrm{CR}_M$ is the statement: for every positive squarefree $\ell\equiv11\pmod{12}$, if the explicit
2-Selmer system of $E_\ell:y^2=x(x-\ell)(x+3\ell)$ has eight elements and contains $(\beta,1)$, then
$(\beta,1)$ is the Kummer class of a rational point of $E_\ell$.

Let $P$ be a property of elliptic curves over $\mathbb Q$, standing for $2^\infty$-Selmer corank one.
Assume Theorem 5.3 for $P$, Lemma 5.4 at the curves $E_\ell$ for $P$, and the rank half of Lemma 5.5 (an
elliptic curve over $\mathbb Q$ with analytic rank one has rank one). Then $\mathrm{CR}_M$ holds.

**Proof sketch.** For such $\ell$, Lemma 5.4 gives $P(E_\ell)$, Theorem 5.3 gives analytic rank one, and
Lemma 5.5 gives rank one, so $E_\ell(\mathbb Q)$ has a point of infinite order. With
$\#E_\ell(\mathbb Q)[2]=4$ and Mordell–Weil for $E_\ell$ (proved), $E_\ell(\mathbb Q)/2E_\ell(\mathbb Q)$ has eight
elements. Its Kummer image lies in the explicit system, which also has eight elements, so the Kummer map is
onto and $(\beta,1)$ comes from a point. The manuscript reaches the same point through the finiteness of
the Tate–Shafarevich group; this count uses only the rank.

## Depends on

- [Theorem 5.3: the restricted converse](../restricted-converse/restricted-converse.md)

## Sources

- [Section 5.1](../../sources/manuscript.md#section-51)
- [Lemma 5.4](../../sources/manuscript.md#lemma-54)
- [Lemma 5.5](../../sources/manuscript.md#lemma-55)
