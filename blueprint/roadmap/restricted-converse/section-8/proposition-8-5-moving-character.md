---
article_id: af_727d0251398c03db61077d2c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3E1RingClass.moving_character_genuine
---

# Proposition 8.5: one moving character for the whole active list

Assume Serre's open image theorem (`SerreThm3`, PRINT), a printed result that is not an input of the
reduction of Theorem 5.3; that rational CM $j$-invariants are integers (`CMjInteger`, GLUE); $\ell>0$; the trace
dictionary at good primes (`FrobeniusTrace`, a hypothesis of the theorem that is proved on this tree as
`frobeniusTrace_proved`); and the remaining fields of the moving data over the genuine ring-class objects
(`GenuineMovingInputs`: generation of the class group, the Kummer relations, the exact ring-class
sequence, the inertia group and the power-residue formula; GLUE, except one field on the Kummer
relations, of kind ELLIOT and GLUE).

Let $E=E_\ell$, $K$ a number field with chosen pairs of primes $\mathfrak p_j\bar{\mathfrak p}_j=(p_j)$
(`RingClassSetup`), the active ones among them, and the places over $2N$, and let $n$ and $\sqrt D$ be
those of the inputs. Then for every $B$ and every finite set of excluded primes there are an odd prime $r$
of good reduction outside it, split in $\mathbb Q(\sqrt D)$, with $r\equiv1\pmod{2^B}$, and a character
$\xi:G_{K,S_r}\to\mathbb Z/2^n$ such that

- $\xi$ takes every value on the inertia group at the place over $r$;
- $\xi$ is trivial on the decomposition groups at the places over $2N$;
- $\xi$ is $1$ at every arithmetic Frobenius at an active prime and $-1$ at its conjugate;
- with $c_E=16d+21$ for the level $d$ of Serre's open image,
  $$v_2(2\pm a_r)\le c_E,\qquad v_2(1\pm a_r+r)\le c_E.$$

The manuscript's character is on $\operatorname{Gal}(H_r/K)$; the Lean character is on $G_{K,S_r}$, and
its factorization through $H_r$ is part of its construction, not of the statement. The manuscript's $K$ is
imaginary quadratic and $r$ splits in it; in Lean $K$ is any number field with a `RingClassSetup`, not tied
to the $\sqrt D$ of the inputs, and "split" is an arithmetic Frobenius at $r$ fixing $\sqrt D$
(`GoodPrime`), which is splitting in $\mathbb Q(\sqrt D)$ only when the excluded set of the inputs
contains the primes ramified there. The exponent $n$ is a parameter of the inputs
(`GenuineMovingInputs E n C`, whose Kummer data are at level $n$), so the theorem is stated at that $n$
rather than for every $n$. The bound on $v_2\det(1\pm\operatorname{Fr}_r)$ appears as the bound on
$v_2(1\pm a_r+r)$, its value. "Infinitely many $r$" is the existence of $r$ outside every finite set.

The reduction of Theorem 5.3 does not use this theorem: the field `PostLeaves.calibration` of [the
remaining hypotheses](../remaining-hypotheses.md) asks for a moving prime of this output form as part
of its data, used in [Proposition 8.9](proposition-8-9-central-calibration.md).

**Proof sketch.** The relations among the chosen primes in the class group give radicands
$\alpha_a=\beta_a/\bar\beta_a$, and prescribing the roots of unity (4.4a) on their $2^n$-th roots
respects every Kummer relation. By the presentation of the ring-class group, $\xi(q_j)=w_j$ and
$\xi\delta=\kappa_r$ extend exactly when (4.4b) holds (`ringClass_extends_iff`). Serre's open image
gives a level $d$ with $\Gamma_{8d+10}$ in the image of the radical-fixing Galois group, (4.4c)
(`four_four_c`), and one of the four matrices of (4.4d) has both trace distances to $\pm2$ of valuation
at most $c_E$ (`trace_lemma`). Chebotarev in a finite extension then gives $r$ with the prescribed
radical Frobenius and trace.

## Depends on

- [Section 8: actual classes, local conditions and central comparison](README.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
