---
article_id: af_0043ba08f65aae62fe95f838
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.slopeRepresentationAP_of_goodPrimeAP
---

# Proposition AP: progressions of good slope primes give the slope representation

Assume 22P_AP. Then the slope representation under field 2′ holds: every integer $A$ is a sum of
three rationals satisfying conditions 1, 2′, 3, 4 for $B_0=0$.

**Proof sketch.** Put $A'=A+10$, $T=\mathcal C\cup\{1\}$ and $S_A^+=T\cup(A'-T)$, so that
$\max S_A^+=\max(1,A'+60)$ and $\min S_A^+=\min(-60,A'-1)$. Take a progression
$x+jv$ ($0\le j\le K_A$, $K_A=\max S_A^+-\min S_A^+$) of good slope primes above $\max S_b$ and put
$u=x+(\max S_A^+)v$. For $c'\in S_A^+$ the number $u-c'v=x+(\max S_A^+-c')v$ is a term of the
progression. Put $t_1=u/v$, $t_2=A'-u/v=(A'v-u)/v$ and $t_3=-10$, so $t_1+t_2+t_3=A$.
Then $t_1>\max S_A^+\ge1$ and $t_2=A'-\max S_A^+-x/v<-60$, so $F(t_1),F(t_2)>0$. The numerators
of $t_1$ are $u-bv$ and those of $t_2$ are $-(u-(A'-b)v)$ ($b\in T$), all terms of the
progression, so both slopes satisfy field 2′ by the lemma on slopes with prime numerators. The
constant $-10$ is a good slope (as in the two-slope pattern), hence satisfies field 2′.

Only fourteen terms of the progression are used. Field 2′ cannot be avoided: a progression of
$K+1$ primes larger than $K+1$ has its difference divisible by every prime at most $K+1$, and
$K_A$ grows with $|A|$.

## Depends on

- [The statement 22P_AP: long progressions of good slope primes](good-prime-ap.md)
- [The slope representation under field 2′](slope-representation-ap.md)

## Proof depends on

- [A slope with prime numerators satisfies field 2′](progression-slope.md)
- [The two-slope pattern gives the slope representation](../multiplication/completeness/slope-representation-from-two-slope.md)
- [The slope representation implies its form under field 2′](slope-representation-ap-of-slope-representation.md)

## Sources

- [The progression form](../../sources/route-ap-locators.md#the-progression-form)
