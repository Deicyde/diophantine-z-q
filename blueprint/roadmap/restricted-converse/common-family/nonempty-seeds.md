---
declaration: theorem
origin: cited
---

# The branch split and the nonempty seeds

If the intrinsic odd limit symbol is a unit at the empty configuration, then
$\operatorname{ord}_{s=1}L(E,s)=1$.

Otherwise, choose a negative even unit $k$, a unit of a separate even symbol on negative discriminants that
are squares at $2N$, avoiding the fixed odd support, the ramification of $E[8]$ and the fields with extra
units, and with a prime ramified in $K=\mathbb Q(\sqrt k)$ outside all old label extensions. Fix $K$ before
the address dimension. Then $L(E^{(k)},1)\ne0$, and $E/K$ has $2^\infty$-Selmer corank one:
$$s_2(E/K)=s_2(E/\mathbb Q)+s_2(E^{(k)}/\mathbb Q)=1.$$
The even source transported to $E^{(k)}$ and normalized at index $1$ satisfies $v_2a_{\rm new}(D)\ge\omega(D)$
on its positive square-unit filter and has a nonempty unit seed of primes split in $K$. The odd symbol too
has a nonempty unit seed, and both seeds can be read through one common alphabet whose projections onto the
two intrinsic alphabets are separately surjective.

**Proof sketch.** In the first branch choose an actual stage carrying the unit with $M_\theta>\delta_o$;
the index $D=1$ lies in every moving support and has $v_2a_{M_\theta}(1)=\delta_o<M_\theta$, so (O.8) gives
the simple zero. In the second branch the bounded-weight witness supplies a least nonempty odd seed. The
unit $k$ has $L(E^{(k)},1)\ne0$ by (3.3a). The fresh ramified prime of $K$ makes $K$ meet the old odd label
extension only in $\mathbb Q$, so every old label still has a lift split in $K$, and makes $K$ independent of
$\mathbb Q(E[8])$, $\mathbb Q(i)$ and $\mathbb Q(\sqrt\ell)$. The forward rank-zero case of Lemma 5.5 gives
$s_2(E^{(k)}/\mathbb Q)=0$, and the sum-and-difference isogeny from the restriction of scalars of $E$ to
$E\times E^{(k)}$, whose kernel and cokernel are killed by a fixed power of $2$, gives the sum formula after
tensoring the compact Selmer modules with $\mathbb Q_2$. Waldspurger's comparison gives
$v_2a_{\rm new}(D)=v_2a_{\rm old}(d_kD)-v_2a_{\rm old}(d_k)\ge\omega(D)$.

For the $K$-split seed suppose there is none. The integral coefficient divisions and a trace identity
$U_p^2t(\phi)=U_p^3+d(\phi)U_p$ with a fresh prime (G.4a)–(G.4d) show that the $p^3$ coefficient is even.
The recurrence gives $a(p^2)=\eta(p)(a_p-1)$ and $a(p^4)=\eta(p)^2\{a_p(a_p-1)-p\}$, so that coefficient is
$\eta^2(a_p-1)(a_p-p-1)/4$, and its evenness forces $a_p\equiv p+1\pmod8$ at every fresh good prime $p$ split in
$K$. Now take such a $p$ with $p\equiv1\pmod4$, $(\ell/p)=-1$ and $(k/p)=1$, which the fresh ramification of
$K$ allows. The reductions of $E^{(k)}$ and $E_\ell$ are isomorphic over $\mathbb F_p$, and none of the three
points of order two is divisible by two, because the square differences $-\ell$, $\ell$, $-4\ell$ are
nonsquares mod $p$. So the $2$-primary part of $E_\ell(\mathbb F_p)$ has order exactly $4$ and
$v_2(p+1-a_p)=2$, a contradiction. This step uses the particular curve $E_\ell$.

## Depends on

- [The odd minimum and the intrinsic odd symbol](odd-minimum.md)
- [An actual even form with rational normalized phase](../coefficient-sources/even-form.md)
- [Finite realization, unit seeds and contraction certificates](seeds.md)

## Proof depends on

- [Visibility and the native genus index (O.8)](../coefficient-sources/visibility.md)
- [The partitionable even upper estimate (3.3b)](even-upper.md)
- [Arithmetic realization of the coefficient rules](coefficient-rules.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): the branch split (L2584–2594), the final companion
  (L2595–2615), $s_2(E/K)=1$ (L2616–2626), `ex:sec7-ksplit-seed` (L2628–2654), `ex:app-nonempty-seeds`
  (L10258–10506)

## Manuscript check

Checked by AI review. The first branch was checked relative to (O.8), which covers $D=1$ explicitly
(L8261–8266, L9189–9190). The corank identity $s_2(E/K)=1$ was checked. Every displayed coefficient formula
of the mod $8$ computation was checked by script, and the claim that the $2$-primary part of
$E_\ell(\mathbb F_p)$ has order exactly $4$ under these conditions was confirmed by brute force over 1,028
pairs $(\ell,p)$. The derivation of the parity of the $p^3$ coefficient from the absence of a seed
(L10323–10452) was read for structure and is not yet checked line by line.
