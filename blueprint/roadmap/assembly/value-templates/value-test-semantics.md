---
article_id: af_c12e743750678945c2261197
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.valueTest_rel_iff
---

# Semantics of the value-test template

Assume the six-contact estimate, pole completeness and the twenty-two-prime
pattern. Then for all $N,K\in\mathbb Q^5$ and $t\in\mathbb Q$,
$$\mathrm{Rel}_{\mathtt{value.test}}(N,K,t)\iff\exists\,n,\kappa\in\mathbb Z:\ N=\iota(n),\ K=\iota(\kappa),\ \operatorname{Test}(n,\kappa,t).$$

**Proof sketch.** The template is $\kappa(\varphi)^2$ for the conjunction $\varphi$ listed in its
definition; its calls ($\mathtt{member}$ seven times, $\mathtt{multiply}$, $\mathtt{raw\_add}$ twice,
$\mathtt{pole}$) have pairwise disjoint blocks occurring in no parameter, so by the
private-witness lemma the relation holds exactly when the fresh variables can be chosen so
that every conjunct holds with each call replaced by its relation. Read the conjuncts in
order.

1. Membership of $N,K,C_1,H,U,V_0,V_1$ gives $N=\iota(n)$, $K=\iota(\kappa)$, $H=\iota(h)$,
   $U=\iota(s_0)$ and $C_1,V_0,V_1$ canonical.
2.  The first coordinate of $K$ is $0$ (written $K[0]=0$; not to be confused with the field
   $K_0$), so $\kappa\ne0$. Statement M gives $C_1=\iota(\kappa n)$. Since
   $\operatorname{neg}(\iota(m))=\iota(-m)$, raw addition gives $V_0=\iota(h-\kappa)$ and
   $V_1=\iota(s_0-\kappa n)$. $H[0]=0$ and $V_0[0]=0$ give $h\ne0$ and $h\ne\kappa$.
3. For each of $H,U,V_0,V_1$ the gadgets $I\!X$ and $Z$ are satisfiable and force the pairs
   $w_i$, $\zeta_i$ to be $w$ and $z$ of the point (nonzero multiples have $x,y\ne0$; the
   identity gives $0$).
4. The two ratio conjuncts are satisfiable because $z(H),z(V_0)\ne0$, and force
   $[\rho_0]=z(U)/z(H)$ and $[\rho_1]=z(V_1)/z(V_0)$. Hence the six pairs $\Delta_i$ are
   $D_1,\dots,D_6$ (conjugation is the pair conjugate).
5. $Fu_F=1$ says $F(t)\ne0$, that is $t\notin\mathcal C$; then $\eta^2=1$, $R_0$, $a_0\ne0$ and $R$ are
   as in the definition of the tests.
6. $F\,C'_i=\Delta_i$ forces $[C'_i]=C_{i+1}=D_{i+1}/F(t)$.
7. The inverse conjunct for $W$ says $W\ne0$ and $[\omega]=W^{-1}$, so
   $\Theta=2\omega_0=\operatorname{Tr}(W^{-1})$; $\Theta u_\Theta=1$ says $\Theta\ne0$; $B\Theta^2=R$ gives
   $B=R/\Theta^2$; and the pole relation is $\Phi(B)$, since the pole template is
   $Q_{\rm pole}^2$.

Conversely, given $n,\kappa$ with $\operatorname{Test}(n,\kappa,t)$ and its $h,s_0,\eta,q$, assign the
forced values; statement M (completeness), raw addition and membership supply the call
relations.

## Depends on

- [The value-test template](../../syntax/templates/template-value-test.md)
- [The six local tests](six-local-tests.md)
- [Point codes](../../model/point-codes.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)
- [Pole completeness](../../main/pole-completeness.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [Accepted inputs have unique indices](../../model/membership-indices.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)
- [Raw addition](../../model/raw-addition.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)
- [Pair arithmetic represents the quadratic field](../../syntax/field-pair-arithmetic.md)
- [Inverse witnesses](../../syntax/nonzero-gadgets.md)
- [The pole template](../../syntax/templates/template-pole.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Template construction from formulas](../../syntax/language/builder-soundness.md)
- [Witness scope of constructed templates and recipes](../../syntax/language/builder-well-formed.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Section 11.2 six local tests](../../../sources/assembly-locators.md#section-112-six-local-tests)
- [Saved specification outer recipes](../../../sources/assembly-locators.md#saved-specification-outer-recipes)
