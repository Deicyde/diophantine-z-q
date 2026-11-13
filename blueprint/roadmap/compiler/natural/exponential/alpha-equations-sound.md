---
article_id: af_0ea487f5ad964c14627b7c25
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaEqns_sound
---

# Soundness of the alpha formula

For all natural numbers $X,b,N$: if $\mathrm{Alpha}(X,b,N)$ holds then $b>3$ and
$X=\alpha_b(N)$.

**Proof sketch.** Fix witnesses $r,s,t,u,v,w,x,y$.

1. *Shapes.* From $u^2+t^2=1+but$ and $b>2$, $u=\alpha_b(k)$ for some $k$ (unordered Pell
   classification); $u>2X\ge0$ gives $u\ge1$, hence $k>0$. From $s^2+r^2=1+bsr$ with
   $r<s$, $(r,s)=(\alpha_b(m-1),\alpha_b(m))$ with $m>0$ (ordered classification). From
   $x^2+y^2=1+wxy$ and $w>2$, $x=\alpha_w(n)$ for some $n\in\mathbb N$.
2. *$u\mid m$.* $u^2\mid s$ is $\alpha_b(k)^2\mid\alpha_b(m)$ with $m>0$; by (C.1)
   $k\,\alpha_b(k)\mid m$, so $u\mid m$.
3. *Residues.* $v+2r=bs$ identifies $v=\alpha_b(m+1)-\alpha_b(m-1)$ (the companion). Parameter
   congruence with $w\equiv b\pmod v$ gives $x\equiv\alpha_b(n)\pmod v$; with
   $w\equiv2\pmod u$ and $\alpha_2(n)=n$ it gives $x\equiv n\pmod u$.
4. *Recover $X$.* Fold $n$ as $n=2lm\pm j$ with $0\le j\le m$. By period and reflection,
   $\alpha_b(n)\equiv\pm\alpha_b(j)\pmod v$, so $X\equiv x\equiv\pm\alpha_b(j)\pmod v$. Both $X$
   and $\alpha_b(j)$ are nonnegative and below $v/2$ ($2X<v$ by hypothesis, $2\alpha_b(j)<v$
   by the companion bound for $b>3$, $j\le m$), so $v\mid X-\alpha_b(j)$ or
   $v\mid X+\alpha_b(j)$ forces $X=\alpha_b(j)$ (in the second case both are $0$).
5. *Recover $N$.* $j\le\alpha_b(j)=X$, so $2j\le2X<u$; also $2N<u$. Since $u\mid m$, the folded
   form gives $n\equiv\pm j\pmod u$, and $N\equiv x\equiv n\pmod u$. Two residues below
   $u/2$ that agree up to sign modulo $u$ are equal: $N=j$. Hence $X=\alpha_b(N)$.

The natural-subtraction case $n=2lm-j$ requires $0<j<2lm$, which the folding lemma
supplies.

## Depends on

- [The alpha formula](alpha-equations.md)
- [The alpha sequence](alpha-sequence.md)

## Proof depends on

- [Natural solutions of the alpha Pell equation](alpha-pell.md)
- [Divisibility of alpha values](alpha-divisibility.md)
- [Parameter congruence of the alpha sequence](alpha-parameter-congruence.md)
- [Period and reflection modulo the companion](alpha-period.md)
- [Growth of the alpha sequence](alpha-growth.md)

## Sources

- [Section 10.2 alpha soundness](../../../../sources/compiler-natural-locators.md#section-102-alpha-soundness)
