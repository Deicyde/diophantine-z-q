---
article_id: af_3f186c028871880047a7d2e0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.exceptions_rel_iff
---

# Semantics of the exceptional values

For all $N\in\mathbb Q^5$ and $t\in\mathbb Q$,
$$\mathrm{Rel}_{\mathtt{value.exceptions}}(N,t)\iff\exists\,c\in\mathcal C:\ N=\iota(c)\ \text{and}\ t=c,$$
where $\mathcal C=\{0,-15,-20,-24,-30,-60\}$.

**Proof sketch.** The polynomial is the sum of the squares of the three generator equations
and of $\kappa(\varphi)$ with
$\varphi=\bigwedge(\langle\mathtt{member}[N]\rangle,\bigvee_{c\in\mathcal C}\beta_c)$. The generator equations,
outside the disjunction, force $G=\iota(1)$, hence $\operatorname{neg}(G)=\iota(-1)$. By the
private-witness lemma the relation holds exactly when $N$ is accepted by membership and,
for some $c\in\mathcal C$, the fresh points of the chain of $\beta_c$ can be chosen with all its
raw-addition relations, $N$ equal to the chain value and $t=c$. The chain of $\beta_c$ is the
chain for $k=|c|$ on $G$ ($c=0$) or on $\operatorname{neg}(G)$ ($c<0$), so by the chain lemma its value
is $\iota(|c|)$ or $\iota(-|c|)$, that is $\iota(c)$ in both cases, and the chain is satisfiable.
Hence a branch $\beta_c$ holds exactly when $N=\iota(c)$ and $t=c$. Membership of $\iota(c)$ holds
by the accepted-indices statement; the witnesses of the inactive branches are arbitrary.

## Depends on

- [The exceptional-values template](../../syntax/templates/template-exceptions.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Double-and-add chains](double-and-add-chains.md)
- [Accepted inputs have unique indices](../../model/membership-indices.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)
- [Rational constants by global equations](../../syntax/language/rational-constants.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Template construction from formulas](../../syntax/language/builder-soundness.md)
- [Witness scope of constructed templates and recipes](../../syntax/language/builder-well-formed.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Section 11.3 exact ordinary value](../../../sources/assembly-locators.md#section-113-exact-ordinary-value)
- [Section 10.4 translation](../../../sources/assembly-locators.md#section-104-translation)
