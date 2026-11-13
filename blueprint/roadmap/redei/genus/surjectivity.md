---
article_id: af_d7528252d09806f35309869d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.exists_chi_eq, ZInQ.RouteK.Redei.prod_ite_bit_eq, ZInQ.RouteK.Redei.jacobiSym_finsetProd_right, ZInQ.RouteK.Redei.ne_two_of_mem_primeFactors
---

# The genus characters take all allowed values

Let $n$ be odd and squarefree, and let $\varepsilon$ assign a bit $\varepsilon_q\in\mathbb F_2$ to
each prime $q\mid n$, with $\sum_q\varepsilon_q=0$ if $n\equiv3\pmod4$. Then there is an ideal
class $c$ of $\mathbb Q(\sqrt{-n})$ with $\chi_q(c)=\varepsilon_q$ for every prime $q\mid n$.

Along the way:

- $\prod_i(-1)^{f_i}=(-1)^{\sum_if_i}$ for finitely many bits $f_i\in\mathbb F_2$;
- for an integer $a$ and finitely many nonzero natural numbers $m_i$, the Jacobi symbol satisfies
  $\bigl(a/\prod_im_i\bigr)=\prod_i(a/m_i)$;
- the primes dividing an odd number are different from $2$.

**Proof sketch.** The primes $q\mid n$ are odd. By the slot lemma there is a prime $\ell\nmid n$
with $[\ell/q]=\varepsilon_q$ for every $q\mid n$, and with $\ell\equiv1\pmod8$ if
$\sum_q\varepsilon_q=0$ and $\ell\equiv3\pmod8$ otherwise; so $\ell$ is odd. As
$n=\prod_{q\mid n}q$, multiplicativity gives $(\ell/n)=\prod_q(\ell/q)=(-1)^{\sum_q\varepsilon_q}$.
Then $(-n/\ell)=\chi_4(\ell)\,(n/\ell)$, and Jacobi reciprocity gives $(-n/\ell)=1$:

- if $\sum_q\varepsilon_q=0$, then $\ell\equiv1\pmod4$, so $\chi_4(\ell)=1$ and $(n/\ell)=(\ell/n)=1$;
- otherwise $n\equiv1\pmod4$ by the hypothesis on $\varepsilon$, and $\ell\equiv3\pmod4$, so
  $\chi_4(\ell)=-1$ and $(n/\ell)=(\ell/n)=-1$.

So $-n$ is a square modulo $\ell$, and $\mathcal O$ has a nonzero ideal $P$ of norm $\ell$. As
$q\nmid\ell$ for every $q\mid n$, its class has $\chi_q([P])=[\ell/q]=\varepsilon_q$.

## Depends on

- [The genus characters](genus-characters.md)

## Proof depends on

- [Split primes](split-primes.md)
- [The slot lemma](../../route-k/slot-lemma.md)
- [Residue bits](../../route-k/residue-bits.md)
- [Quadratic reciprocity in residue bits](../../route-k/reciprocity-bits.md)

## Sources

- [Step 5: Dirichlet's theorem](../../../sources/redei-locators.md#step-5-dirichlets-theorem)
- [The chosen route](../../../sources/redei-locators.md#the-chosen-route)
