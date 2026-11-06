---
article_id: af_ee7c744135cbe476176a5e17
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.valueTestTemplate, ZInQ.Syntax.valueTest_facts
---

# The value-test template

The template $\mathtt{value.test}$ has $11$ parameters and $35282$ witnesses ($35293$
variables). Parameters: points $N=(X_0,\dots,X_4)$, $K=(X_5,\dots,X_9)$ and $t=X_{10}$.
Witnesses in allocation order:

- points $C_1,H,U,V_0,V_1$ at $X_{11},\dots,X_{35}$ (five each);
- $\mathtt{member}$ blocks for $N,K,C_1,H,U,V_0,V_1$ at $36,43,50,57,64,71,78$;
- a $\mathtt{multiply}$ block $[85,35219)$ and $\mathtt{raw\_add}$ blocks $[35219,35225)$,
  $[35225,35231)$;
- for $i=0,\dots,3$ and $\Pi=(H,U,V_0,V_1)$, with base $b=35231+5i$: pairs
  $w_i=(X_b,X_{b+1})$, $\zeta_i=(X_{b+2},X_{b+3})$ and the inverse witness $X_{b+4}$ of
  $Z(\Pi_i,\zeta_i)$;
- ratio pairs $\rho_0=(X_{35251},X_{35252})$ with inverse witness $X_{35253}$ and
  $\rho_1=(X_{35254},X_{35255})$ with inverse witness $X_{35256}$;
- $\eta=X_{35257}$, $q=X_{35258}$, $R_0=X_{35259}$, $a_0=X_{35260}$, $R=X_{35261}$, inverse
  witnesses $u_F=X_{35262}$, $u_a=X_{35263}$;
- normalized pairs $C'_0,\dots,C'_5$ at $X_{35264},\dots,X_{35275}$;
- $\omega=(X_{35276},X_{35277})$ with inverse witness $v_W=X_{35278}$; $\Theta=X_{35279}$,
  $B=X_{35280}$, $u_\Theta=X_{35281}$; and a $\mathtt{pole}$ block $[35282,35293)$.

Let $F=(t-0)(t+15)(t+20)(t+24)(t+30)(t+60)$ (left to right),
$\Delta=(w_0,\ w_1,\ \bar w_2,\ \bar w_3,\ \rho_0-(t,0),\ \bar\rho_1-(t,0))$ and
$W=\prod_{i=0}^5(1+R\,C_i'^{\,2})$ in pair arithmetic. The formula is the conjunction of, in this
order:

1. $\langle\mathtt{member}[N]\rangle$, $\langle\mathtt{member}[K]\rangle$,
   $\langle\mathtt{member}[C_1]\rangle$, $\langle\mathtt{member}[H]\rangle$,
   $\langle\mathtt{member}[U]\rangle$, $\langle\mathtt{member}[V_0]\rangle$,
   $\langle\mathtt{member}[V_1]\rangle$;
2. $\mathrm{fin}(K)$, $\langle\mathtt{multiply}[K,N,C_1]\rangle$,
   $\langle\mathtt{raw\_add}[H,\mathrm{neg}(K),V_0]\rangle$, $\langle\mathtt{raw\_add}[U,\mathrm{neg}(C_1),V_1]\rangle$,
   $\mathrm{fin}(H)$, $\mathrm{fin}(V_0)$;
3. for $i=0,\dots,3$: $I\!X(\Pi_i,w_i)$ and $Z(\Pi_i,\zeta_i)$;
4. $\bigwedge(N(\zeta_0)\,v_0'\doteq1,\ \zeta_0\cdot\rho_0\doteq\zeta_1)$ and
   $\bigwedge(N(\zeta_2)\,v_1'\doteq1,\ \zeta_2\cdot\rho_1\doteq\zeta_3)$, with $v_0'=X_{35253}$,
   $v_1'=X_{35256}$;
5. $F\,u_F\doteq1$, $\eta^2\doteq1$, $R_0\doteq\eta\cdot2730^6\cdot F$, $a_0\doteq1-R_0q^2$,
   $a_0u_a\doteq1$, $R\doteq R_0a_0^2$;
6. $F\,C_i'\doteq\Delta_i$ for $i=0,\dots,5$ (pair equations);
7. $\bigwedge(N(W)\,v_W\doteq1,\ W\cdot\omega\doteq(1,0))$, $\Theta\doteq2\omega_0$,
   $\Theta u_\Theta\doteq1$, $B\Theta^2\doteq R$, $\langle\mathtt{pole}[B]\rangle$.

The polynomial is $\kappa$ of this conjunction, squared. Here
$2730^6=413976684737889000000$.

These are the six raw field-valued tests and the single pole predicate of the
variable-shift relation (Section 11).

This is a definition (template index $16$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [The membership template](../template-member.md)
- [The multiplication template](template-multiply.md)
- [The raw addition template](../template-raw-add.md)
- [The pole template](template-pole.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
