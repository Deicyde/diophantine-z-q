---
article_id: af_f8579c4422080739c7aa7651
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.search_box
---

# The search box for small heights

Let $x\in K_0$ with $h(x)<\log9$.

1. If $x\in\mathbb Q$, then $x=p/q$ with $p,q\in\mathbb Z$ coprime, $|p|\le9$ and $1\le q\le9$
   (in fact $|p|,q\le8$).
2. If $x\notin\mathbb Q$, then there are integers $a,b,c,k$ with
   $$1\le a\le81,\quad|b|\le162,\quad|c|\le81,\quad\gcd(a,b,c)=1,\quad b^2-4ac=2k^2,\quad
   1\le k\le162,$$
   such that $x=\frac{-b+ks}{2a}$ or $x=\frac{-b-ks}{2a}$; then $aX^2+bX+c$ is the primitive
   minimal polynomial of $x$ and both its roots lie in $K_0$.

**Proof sketch.** (1) $h(p/q)=\log\max(|p|,q)<\log9$. (2) Write $x=u+vs$ with $v\ne0$ and
$x=\alpha/\beta$ with $\alpha,\beta\in\mathbb Z[s]$ coprime. The integer polynomial
$f(X)=\operatorname N(\beta X-\alpha)=\operatorname N(\beta)X^2-\operatorname{Tr}(\alpha\bar\beta)X+\operatorname N(\alpha)$
has the real roots $r_\pm=\sigma_\pm(x)$, and
$|\operatorname N(\beta)|\max(1,|r_+|)\max(1,|r_-|)=\prod_\sigma\max(|\sigma\alpha|,|\sigma\beta|)=e^{2h(x)}<81$.
Divide $f$ by its content and fix the sign to get $aX^2+bX+c$ with $a\ge1$ and
$a\max(1,|r_+|)\max(1,|r_-|)<81$. Then $a<81$, $|b|=a|r_++r_-|<162$ and $|c|=a|r_+r_-|<81$.
The discriminant is $a^2(r_+-r_-)^2=8a^2v^2=2k^2$ with $k=2a|v|>0$; as $2k^2\in\mathbb Z$ and
$k\in\mathbb Q$, $k\in\mathbb Z$, and $2k^2<162^2+4\cdot81^2=2\cdot162^2$ gives $k<162$. Finally
$2au=-b$ and $2av=\pm k$.

## Depends on

- [The $x$-height on $C(K_0)$](x-height.md)

## Proof depends on

- [The height of a fraction in $\mathbb Z[\sqrt2]$](x-height-formula.md)
- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](../field/integers-pid.md)

## Sources

- [Finite search](../../../sources/model-locators.md#finite-search)
