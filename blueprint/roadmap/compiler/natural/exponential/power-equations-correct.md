---
article_id: af_59e30837b7f41c26e293c453
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.powEqns_iff
---

# The power formula expresses exponentiation

For all natural numbers $P,Q,R$:
$$\mathrm{Pow}(P,Q,R)\iff P=Q^R,$$
with $0^0=1$. This includes $R=0$, $Q=1$ and the base $Q=0$.

**Proof sketch.** If $Q=0$ the third branch is excluded and the first two say exactly
$P=0^R$. Let $Q\ge1$; only the third branch can hold.

*Forward.* By alpha soundness, $a_0=\alpha_{Q+4}(R+1)$; then $b=a_0+Q^2+2\ge4$, so the two
other alpha formulas give $a_1=\alpha_b(R)$, $a_2=\alpha_b(R+1)$. By growth,
$a_0\ge(Q+3)^R$, and therefore $m=bQ-Q^2-1=(a_0+Q^2+2)Q-Q^2-1>Q^R$, so $m>0$. Put
$U=\alpha_b$ and $E_R=QU_R-bU_R+U_{R+1}$. Then $E_0=1$ and, by the recurrence,
$E_{R+1}-Q^{R+1}=Q(E_R-Q^R)+(bQ-Q^2-1)U_R$, so $m\mid E_R-Q^R$ for every $R$ (as integers;
this needs no sign or size hypothesis). The congruence $P+ba_1\equiv Qa_1+a_2\pmod m$ says
$P\equiv E_R\equiv Q^R\pmod m$; since $0\le P<m$ and $0\le Q^R<m$, $P=Q^R$.

*Backward.* Given $P=Q^R$ with $Q\ge1$, take $a_0=\alpha_{Q+4}(R+1)$, $b=a_0+Q^2+2$,
$m=bQ-Q^2-1$ (natural, and $m>Q^R=P$), $a_1=\alpha_b(R)$, $a_2=\alpha_b(R+1)$; alpha
completeness supplies the three alpha formulas ($Q+4>3$, $b>3$), and the congruence holds by
the divisibility above (in natural numbers, $P+ba_1$ and $Qa_1+a_2$ have equal remainders
modulo $m$ because $Qa_1+a_2-ba_1=E_R$ is congruent to $P$).

## Depends on

- [The power formula](power-equations.md)

## Proof depends on

- [Soundness of the alpha formula](alpha-equations-sound.md)
- [Completeness of the alpha formula](alpha-equations-complete.md)
- [Growth of the alpha sequence](alpha-growth.md)

## Sources

- [Section 10.2 power formula](../../../../sources/compiler-natural-locators.md#section-102-power-formula)
