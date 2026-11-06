---
article_id: af_7af9f97e362247eb9960ab20
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.decide5_iff, ZInQ.Compiler.Precision.decideInt_iff
---

# Correctness of the decision program

For every $c\in\mathbb N^5$, $\mathrm{decide}(c)=\mathrm{true}\iff\operatorname{accepts}(c)$.
The program terminates on every input, including every early rejection.

**Proof sketch.** Step 1 is item 1 of the relation (signed decoding). Step 2: by the
scalar-multiplication statement, $Z_k=0$ iff $[k]P_0=O$ and, for $Z_k\ne0$, $Y_k=0$ iff the
ordinate vanishes; so step 2 passes iff $l,a,j$ are admissible. Step 3: $z_k=-x/y=-X_kZ_k/Y_k=\nu_k/N_k$
with $N_k=\operatorname N(Y_k)\ne0$ by the norm-zero statement; $\epsilon_l=(|p|+|p'|)/|N_l|$,
and $U>0$ because $z_l\ne0$. Step 4: $z_j/z_a=\nu_j\bar\nu_aN_a/(N_j\operatorname N(\nu_a))$, with
$\nu_a\ne0$ so $\operatorname N(\nu_a)\ne0$; then $|\theta/\delta-n|<U/V$ is the displayed integer
inequality after multiplying by $|\delta|V>0$. Step 5: by the threshold statement,
$4\epsilon_l<4^{-\mathcal B}$ iff $4^{\mathcal B}\le L$; if $L=0$ this is false since $4^{\mathcal B}\ge1$;
if $L\ge1$ the capped precision test computes exactly this comparison with
$\mathcal B=A^{(0)}_{\rm ht}M^{24}$. Termination: the scalar loop halves, the factorial and
capped-power loops are bounded, and the precision loop runs at most $L+1$ steps.

## Depends on

- [The exact decision program](decision-program.md)
- [The precision relation](precision-relation.md)

## Proof depends on

- [The signed encoding is a bijection](signed-encoding-bijection.md)
- [Scalar multiplication by halving](jacobian-scalar-multiplication.md)
- [Elements of norm zero](norm-zero.md)
- [The precision threshold as an integer comparison](precision-threshold.md)
- [The capped precision test](capped-height-test.md)

## Sources

- [Section 10 decision predicate](../../../../sources/compiler-natural-locators.md#section-10-decision-predicate)
- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
