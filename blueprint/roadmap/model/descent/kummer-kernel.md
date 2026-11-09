---
article_id: af_96861fc3f38369c439db79a4
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Descent.kummer_eq_one_iff
---

# The image of a two-isogeny is the kernel of the Kummer map

Let $K$ be a field of characteristic different from $2$ and $b\in K^\times$. For
$Q\in E_{-4b}(K)$,
$$\alpha_{-4b}(Q)=1\iff Q\in\varphi_b\bigl(E_b(K)\bigr).$$

**Proof sketch.** (Silverman, Proposition X.4.9; Silverman-Tate, Section III.5.)
($\Leftarrow$) $\varphi_b(O)=\varphi_b((0,0))=O$. For $P=(x,y)$ with $x\ne0$ and $y\ne0$,
the abscissa of $\varphi_b(P)$ is $(y/x)^2$. If $y=0$ and $x\ne0$ then $x^2=-b$ and
$\varphi_b(P)=(0,0)$, whose class $-4b=(2x)^2$ is trivial. ($\Rightarrow$) If $Q=O$ take $P=O$.
If $Q=(0,0)$ and $-4b=t^2$, then $P=(t/2,0)\in E_b(K)$ and $\varphi_b(P)=(0,0)$. If
$Q=(X,Y)$ with $X=w^2\ne0$, then $Y^2/w^2=w^4-4b$, so the quadratic $x^2-w^2x+b$ has the
roots $x_\pm=(w^2\pm Y/w)/2\in K$, both nonzero since $x_+x_-=b$. Put $x=x_-$ and $y=wx$;
then $y^2=w^2x^2=x^3+bx$, and $\varphi_b((x,y))=(w^2,\,w(b-x^2)/x)=(X,Y)$ because
$b-x^2=b-w^2x+b$ and $2b/x=2x_+$.

## Depends on

- [Two-isogenies and the Kummer map](kummer-map.md)

## Sources

- [Descent index](../../../sources/model-locators.md#descent-index)
- [Silverman](../../../sources/model-locators.md#silverman)
