---
article_id: af_6124f10edd6bc9e10b0e74d1
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Assembly.realCurve, ZInQ.Assembly.RealCurve.TendstoPt, ZInQ.Assembly.RealCurve.exists_subseq_tendstoPt, ZInQ.Assembly.RealCurve.tendstoPt_sub_zero
---

# Compactness and continuity of subtraction on a real curve

Let $e\in\mathbb R$, $e\ne0$, and let $E_e(\mathbb R)$ be the group of real points of
$y^2=x^3-e^2x$ (chord-and-tangent law, identity $O$). For a sequence $(P_m)$ in $E_e(\mathbb R)$
and $Q\in E_e(\mathbb R)$ write $P_m\to Q$ when

- $Q=(x_Q,y_Q)$ is affine, $P_m$ is affine for all large $m$, and $x(P_m)\to x_Q$,
  $y(P_m)\to y_Q$; or
- $Q=O$ and for every $M\in\mathbb R$, for all large $m$, either $P_m=O$ or $P_m$ is affine with
  $x(P_m)>M$.

Then:

1. every sequence in $E_e(\mathbb R)$ has a subsequence converging to some point of
   $E_e(\mathbb R)$;
2. if $P_m\to Q$ and $P'_m\to Q$ for the same $Q$, then $P'_m-P_m\to O$.

**Proof sketch.** Write $f(x)=x^3-e^2x=(x+e)x(x-e)$; its roots $0,\pm e$ are simple, with
$f'(c)=3c^2-e^2\ne0$ at each root. Real points have $f(x)\ge0$, so $x\ge-|e|$.

(1) If infinitely many terms are $O$, or the abscissas of the affine terms are unbounded
above, a subsequence converges to $O$. Otherwise the affine terms eventually lie in
$[-|e|,M]\times[-\sqrt{\max f},\sqrt{\max f}]$, and Bolzano–Weierstrass gives a convergent
subsequence; its limit satisfies $y^2=f(x)$ by continuity.

(2) Discard the indices with $P'_m=P_m$, where the difference is $O$. Case $Q$ affine with
$y_Q\ne0$: eventually $y'+y\to2y_Q\ne0$, so $P'\ne-P$; if $x'=x$ then $P'=P$; otherwise
$P'-P=P'+(-P)$ has abscissa $\lambda^2-x-x'$ with chord slope $\lambda=(y'+y)/(x'-x)$, and
$|\lambda|\to\infty$. Case $Q=(c,0)$ with $f(c)=0$: if $x'=x$ then $P'=-P$ and
$P'-P=-[2]P$ has abscissa $\bigl(f'(x)/(2y)\bigr)^2-2x\to\infty$ since $f'(x)\to f'(c)\ne0$ and
$y\to0$; otherwise $y'^2-y^2=(x'-x)\,g$ with $g=x'^2+xx'+x^2-e^2\to f'(c)\ne0$, so
eventually $y'\ne y$ and $\lambda=(y'+y)/(x'-x)=g/(y'-y)$ has $|\lambda|\to\infty$. Case $Q=O$:
translate by $T=(0,0)$. For affine $P=(x,y)$ with $x\ne0$, $P+T=(-e^2/x,\ e^2y/x^2)$, and
$|e^2y/x^2|^2=e^4f(x)/x^4\to0$ as $x\to\infty$, while $O+T=T$; hence $P_m+T\to T$ and
$P'_m+T\to T$, and $(P'_m+T)-(P_m+T)=P'_m-P_m\to O$ by the previous case. In every case the
abscissa of $P'_m-P_m$ tends to $+\infty$ (or the difference is $O$).

This is the elementary content of "$E(\mathbb R)$ is a compact topological group"; the
manuscript uses compactness of $E(\mathbb R)\times E(\mathbb R)$ directly.

## Depends on

None.

## Sources

- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
- [Silverman](../../../sources/assembly-locators.md#silverman)
