---
article_id: af_440fd6c0702e2590e74d6a25
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Even.E12_of_eigenspace, ZInQ.Manuscript.RC.Even.closedForm_of_eigenspace
---

# (E.12): the good $T(p^2)$ recurrence

Assume nothing: the eigenform condition below is a definition (Shimura's operator $T(p^2)$ on Fourier
coefficients), and the Lean theorems take no named input.

Let $4\mid N$, $\sigma=\pm1$, let $\psi,\eta$ be Dirichlet characters modulo $N$ with $\eta=\psi\chi_{-\sigma}$
on integers prime to $N$, and let $g$ be a cusp form of weight $3/2$, level $N$ and character $\psi$ with
$T(p^2)g=\eta(p)a_p(E)g$ for every prime $p\nmid N$. Then for every prime $p\nmid N$ and every $n$,
$$a(p^2n)=\bigl\{\eta(p)a_p(E)-\psi(p)\bigl(\tfrac{-n}{p}\bigr)\bigr\}a(n)-p\,\eta(p)^2a(n/p^2),\tag{E.12}$$
with $a(n/p^2)=0$ when $p^2\nmid n$. Consequently, for squarefree $D>0$ and $m>0$ prime to $N$,
$$a(Dm^2)=\prod_{p^r\Vert m}\eta(p)^rA_{p,r}(D)\cdot a(D),$$
where $A_{p,0}=1$, $A_{p,1}=a_p(E)-\chi_{-\sigma}(p)\bigl(\tfrac{-D}{p}\bigr)$ and
$A_{p,r+1}=a_p(E)A_{p,r}-pA_{p,r-1}$ are integers.

The manuscript states the recurrence at primes outside $S_0\cup B$, after its coprimality sieve by $B$;
in Lean it holds at every prime not dividing the level, for every form of the eigenspace, and the
sieve is not applied to the form. The manuscript's displayed closed form, for its normalized $a$ and
$D$ in the filter, is $a(Dm^2)=z_D\eta(m)r_D\prod_{p^r\Vert m}A_{p,r}(D)$; Lean's form, with the base
coefficient $a(D)$ as a separate factor, equals it by (E.11), $a(D)=z_Dr_D$, since
$\prod_{p^r\Vert m}\eta(p)^r=\eta(m)$. Before that display the manuscript has a slip: it writes
$a(Dp^{2r})=\eta(p)^rb_r$, so $b_0=a(D)$, and says that all are integers, but only the multipliers
$A_{p,r}(D)$ are integers, with $b_r=A_{p,r}(D)\,a(D)$.

**Proof sketch.** The eigenvalue equation for $T(p^2)$ is the displayed identity with $\psi(p)^2$ in the
last term, and $\psi(p)^2=\eta(p)^2$ because $\psi/\eta=\chi_{-\sigma}$ is quadratic. Induction on the prime
factors of $m$ gives the closed form; the other prime-square factors do not change the Legendre
symbol at $p$.

In the Lean proof of Theorem 5.3 this theorem is not used.

## Depends on

None.

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
