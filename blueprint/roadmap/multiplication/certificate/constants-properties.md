---
article_id: af_953e9c644e926a1b8402a947
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.one_le_M0, ZInQ.Mult.one_le_M0_spec, ZInQ.Mult.four_le_cstar, ZInQ.Mult.one_le_ell, ZInQ.Mult.S_mul_admissible, ZInQ.Mult.Aht_eq_heightH6, ZInQ.Mult.sixContact_at_Smul, ZInQ.Mult.four_lt_T, ZInQ.Mult.prime_of_mem_catalogue, ZInQ.Mult.catalogue_injective, ZInQ.Mult.Hcat_squarefree, ZInQ.Mult.padicValNat_ell, ZInQ.Mult.not_mem_S_mul
---

# Properties of the multiplication constants

1. $M_0\ge1$, so $c_*=4M_0\ge4$, and $\ell_0\ge1$.
2. $S_{\rm mul}$ is a finite set of primes containing every prime $p\le324$; every
   $p\in S_{\rm mul}$ satisfies $p\le R$; and $R\ge D$, $R\ge10^{12}$. Hence the six-contact
   estimate applies with $S=S_{\rm mul}$ and this $R$, and its constant is
   $H_6(S_{\rm mul};R)=A_{\rm ht}$ (as real numbers, $Q=R^{RE_0}$ being an integer power). Under
   the minimal height hypothesis, $h(u)\le A_{\rm ht}M_{S_{\rm mul}}(u)^{24}$ for every
   $u\in\mathbb Q\setminus\mathcal C$, since $H_6(D)\le H_6(S_{\rm mul};R)$.
3. $A_{\rm ht}\ge2\cdot10^{13}$; in particular $48A_{\rm ht}\ge1$ and $T=(48A_{\rm ht})^{13}>4$.
4. The catalogue primes exceed $324$ and are pairwise distinct, so $H_{\rm cat}$ is squarefree
   with set of prime factors $\mathcal H$. Consequently $v_p(\ell_0)=E_p$ for $p\in S_b$ and
   $v_p(\ell_0)=0$ for every prime $p\notin S_b$.
5. Every prime $p\notin S_{\rm mul}$ satisfies $p>324$, $p\nmid c_*$, $p\nmid\ell_0$ and
   $p\notin S_0=\{2,3,5,7,13\}$.

No constant is evaluated: every item follows from the defining expressions.

**Proof sketch.** (1) The search defining $M_0$ succeeds at an index at most $N_s^{10}$ (the
successful formal multiple of the size chapter, with $N_s\ge1$), so $M_0\ge1$. (2) Primes of $S_{\rm ht}$ are at
most $324\le10^{12}\le R$; catalogue primes are at most $H_{\max}\le R$ by the definition of the
catalogue maximum; a prime dividing $c_*\ge1$ is at most $c_*\le R$. $S_{\rm mul}$ is finite
because the catalogue is finite and $c_*\ne0$. The six-contact constant at $R$ is
$2\cdot10^{13}\max(1,C_{\rm cm},Q_R^{17})$ with $Q_R=R^{RE_0}$, literally $A_{\rm ht}$; it is increasing in $R\ge1$, and $R\ge D$. (3) is
immediate from the maximum with $1$. (4) Distinct residue classes, or distinct positions in
one class, give distinct primes. Then $v_p(\ell_0)=v_p(12)+2916$ for $p\le324$ and
$v_p(\ell_0)=732$ for $p\in\mathcal H$, which equal $E_p$ by the clearing arithmetic
($C_p=56$, resp. $C_p=14$ and $v_p(12)=0$). (5) $S_{\rm mul}$ contains all primes at most $324$
and all prime divisors of $c_*$ and of $\ell_0$.

## Depends on

- [Prime sets and clearing exponents of the multiplication certificate](constants.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)
- [The minimal height hypothesis](../../main/six-contact-min.md)

## Proof depends on

- [A successful formal multiple](../../size/formal-multiple/formal-multiple-existence.md)
- [The clearing inequalities](clearing-arithmetic.md)
- [The least formal multiple](../../syntax/constants/least-formal-multiple.md)

## Sources

- [Fixed constants](../../../sources/multiplication-locators.md#fixed-constants)
- [Least formal multiple exists](../../../sources/multiplication-locators.md#least-formal-multiple-exists)
- [Contact prime sets](../../../sources/multiplication-locators.md#contact-prime-sets)
