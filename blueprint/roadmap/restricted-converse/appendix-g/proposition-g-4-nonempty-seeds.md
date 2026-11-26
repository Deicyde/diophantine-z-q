---
article_id: af_693910cd64a837201872eb1d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.KSplit.app_nonempty_seed, ZInQ.Manuscript.RC.KSplit.NoSeedTraceData.cong_eight, ZInQ.Manuscript.RC.Wiring.ksplitCongruence_of_traceData, ZInQ.Manuscript.RC.KSplit.dphi_expansion, ZInQ.Manuscript.RC.KSplit.thetaMul_sub_self_inTwoO, ZInQ.Manuscript.RC.KSplit.G4a_of_improved_bound, ZInQ.Manuscript.RC.KSplit.G4b_of_shell, ZInQ.Manuscript.RC.KSplit.transport_lower_bound
---

# Proposition G.4: the nonempty $K$-split seed, (G.4a)–(G.4d)

Let $\ell>0$ be squarefree with $\ell\equiv11\pmod{12}$, let $k$ be odd and squarefree with a prime
$q_0\mid k$, $q_0\nmid2\ell$, let $K=\mathbb Q(\sqrt k)$ and $S$ a finite set of primes, and let
$\mathcal O$ be a subring of a field of characteristic zero. Write $a_p=a_p(E_\ell^{(k)})$. Assume, as
Elliot's coefficient calculation (ELLIOT, a named input), that if the transported even source of
$E^{(k)}$ had no nonempty $K$-split unit seed, every prime $p\notin S$ with $p\nmid6k\ell$ and
$(k/p)=1$ would carry the following *no-seed trace data* (`NoSeedTraceData`):

- coefficients $a(n)$ with $a(1)=1$ obeying the good $T(p^2)$ recurrence (E.12) at $p$ with eigenvalue
  $\eta(p)a_p$ (Shimura's formula, a printed result outside the reduction of Theorem 5.3, used as
  ELLIOT), the positive-twist convention $\psi(p)=\eta(p)(-1/p)$, character values in $\mathcal O$ with
  $\eta(1)=1$ and $\eta(p)$ a unit, $p$ prime to the support, and $1/2\notin\mathcal O$;
- with $B[n]=(a(pn)-\eta(p)a(n/p))/2$, the second term only when $p\mid n$, $b_1=B[1]=a(p)/2$,
  $b_p=B[p]$ and $H=(B-b_1\Theta_1-b_p\Theta_{\{p\}})/2$: $H$ is integral ((O.11) of Appendix F);
- a fresh prime $p'\ne p$ and, for $f=\theta H$, the trace identity
  $(t(\phi)f)[p^2]=f[p^3]+(d(\phi)f)[p]$ and the Hecke formula
  $(t(\phi)f)[p^2]\equiv f[p^2p']\pmod{2\mathcal O}$;
- integral scalars $\delta_B=\delta_p$ and $\delta_1$ by which $d(\phi)$ acts on $\theta B$,
  $\theta\Theta_{\{p\}}$ and $\theta\Theta_1$;
- the no-seed bounds $v_2a(pp')\ge3$ and
$$b_1\in2\mathcal O,\tag{G.4a}$$
$$B[p-j^2]\in2\mathcal O\qquad(0<j^2<p).\tag{G.4b}$$

Then the transported source has a nonempty $K$-split unit seed. The proof proves two displays: the
exact expansion
$$(d(\phi)f)[p]=\frac{\delta_BB[p]-\delta_pb_p}2+\sum_{0<j^2<p}\bigl(\delta_BB[p-j^2]
-\delta_1b_1\Theta_1[p-j^2]-\delta_pb_p\Theta_{\{p\}}[p-j^2]\bigr),\tag{G.4c}$$
and, since $H$ is integral, for every $N$
$$f[N]=H[N]+2\sum_{0<j^2\le N}H[N-j^2]\equiv H[N]\pmod{2\mathcal O}.\tag{G.4d}$$

`G4a_of_improved_bound` derives (G.4a) from $a(p)\in4\mathcal O$ or $a(p)=0$, and `G4b_of_shell`
derives (G.4b) at $n=p-j^2$ from one of: $a(pn)=0$; $a(pn)$ an integral multiple of an element of
$4\mathcal O$; $a(pn)$ an integral multiple of $a(p)$ with $a(p)/2\in2\mathcal O$. These alternatives are
ELLIOT inputs. In the manuscript they come from the improved bound under the no-seed assumption or the
filter, and from the coprimality sieve or the shell recurrences with $v_2a(pr)\ge\omega(pr)$ or with
(G.4a). The print's sieve case reads "If $n_j$ meets the old support", while the support of the
transported source also contains the primes of $k$; the case $q\mid k$, $q^2\mid n_j$ is covered only by
the sieve at that full support. `transport_lower_bound` is the bound $v_2a_{\rm new}(D)\ge\omega(D)$
of the statement, from the Waldspurger comparison
$v_2a_{\rm new}(D)=v_2a_{\rm old}(d_kD)-v_2a_{\rm old}(d_k)$ (ELLIOT), the old lower bound at $d_kD$ and
the old unit condition at $d_k$ (hypotheses; in the manuscript $d_k$ is a unit of the old normalized
symbol), with $d_k$ prime to $D$.

The source and its seeds are not formalized here: the absence of a nonempty seed is an arbitrary
proposition, and the forms and operators enter only through their coefficients, each property used being
a field of the trace data. `ksplitCongruence_of_traceData` turns the trace data into the hypothesis of
[Lemma 7.16](../section-7/lemma-7-16-k-split-seed.md). The other clauses of the proposition are not part
of the statement. In the reduction of Theorem 5.3, the Selmer corank one of $E/K$, stated as corank zero
for $E^{(k)}$ beside corank one for $E$, is proved from the forward theorem at $k$
(`selmerCorankOneOverK_of`); if the odd symbol is a unit at the empty configuration, (O.8) at $D=1$ gives
the simple zero (`rc_of_oddEmptyUnit`); otherwise the bounded-weight odd witness, which gives the
nonempty odd seed, is derived from the attained odd minimum (`oddWitness_of_dataSpec`). The nonempty
$K$-split seed is not taken from this theorem: the reduction applies `exists_unitSeed_of_ksplit`
([Lemma 7.16](../section-7/lemma-7-16-k-split-seed.md)) in `addressInput_of_packageZeroTotal`, and its
hypothesis, the conditional congruence, is the $K$-split seed clause (ELLIOT) of the field
`PostLeaves.address` of [the remaining hypotheses](../remaining-hypotheses.md). `app_nonempty_seed` and
`ksplitCongruence_of_traceData` are not on the reduction path.

**Proof sketch.** The first term of (G.4c) vanishes since $B[p]=b_p$ and $\delta_B=\delta_p$, and each
summand is even by (G.4a), (G.4b) and $\Theta_{\{p\}}[p-j^2]=0$; so $(d(\phi)f)[p]\in2\mathcal O$. By the
Hecke formula and (G.4d), $(t(\phi)f)[p^2]\equiv H[p^2p']=\eta(p)(a_p-1)a(pp')/4$, which is even since
$v_2a(pp')\ge3$. The trace identity and (G.4d) at $p^3$ then give $H[p^3]\in2\mathcal O$. The recurrence
gives $H[p^3]=\eta(p)^2(a_p-1)(a_p-p-1)/4$; as $4\mid a_p-p-1$ by full rational two-torsion, $a_p-1$ is
odd and $\eta(p)$ is a unit, $a_p\equiv p+1\pmod8$. The fresh prime $q_0$ gives such a $p$ with
$v_2(p+1-a_p)=2$, as in Lemma 7.16, a contradiction.

## Depends on

- [Section 7: unit seeds](../section-7/README.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Proof depends on

- [Lemma 7.16: the nonempty $K$-split seed](../section-7/lemma-7-16-k-split-seed.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
