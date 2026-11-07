---
article_id: af_658a048485d8c44de30ea1dd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.close_complete
---

# Completeness of Close for every fixed shift

Assume the six-contact estimate, pole completeness and the twenty-two-prime
pattern. For every $n\in\mathbb Z\setminus\mathcal C$ and every nonzero
$\kappa\in\mathbb Z$,
$$\mathrm{Rel}_{\mathtt{close}}\bigl(\iota(n),\iota(\kappa),n\bigr).$$
The shift $\kappa$ is arbitrary: this holds for every already fixed nonzero $\kappa$, whatever its
size.

**Proof sketch.** Put $B=B(n,\kappa)\in\mathbb N$ and $\theta=4^{-B}/4>0$. By the Close relation it
suffices to find $a,l\ge1$ with $\operatorname{Prec}(n,\kappa,a,l,na)$ and $|n-r(a,na)|<\epsilon_l$; the
latter is one of the conditions of $\operatorname{Prec}$.

*Choice of $l$.* For an affine point with abscissa $x$ and $\tau(x)>|\tau(d)|$ in a real
embedding $\tau$, $\tau(z)^2=\tau(x)/(\tau(x)^2-\tau(d)^2)$, which tends to $0$ as $\tau(x)\to\infty$.
Choose $M_1$ such that $\tau(x)>M_1$ gives $|\tau(z)|<\theta/2$ for both $\tau=\sigma_\pm$, and by the
accumulation statement choose $l\ge1$ with $\sigma_\pm(x([l]P_0))>M_1$. Since
$u_l=(\sigma_+z_l+\sigma_-z_l)/2$ and $v_l=(\sigma_+z_l-\sigma_-z_l)/(2\sqrt2)$,
$$0<\epsilon_l=|u_l|+|v_l|\le|\sigma_+z_l|+|\sigma_-z_l|<\theta,$$
positivity because $z_l\ne0$. Hence $4\epsilon_l\cdot4^{B}<1$.

*Choice of $a$.* Apply the real derivative statement to $n$ with $\eta=\epsilon_l$ in both
embeddings, obtaining $M_2$, and choose $a\ge1$ by accumulation with
$\sigma_\pm(x([a]P_0))>M_2$. With $Q=[a]P_0$ and $[n]Q=[na]P_0$,
$$|r(a,na)-n|=\Bigl|\tfrac12\sum_\pm\bigl(\sigma_\pm(z_{na}/z_a)-n\bigr)\Bigr|<\epsilon_l .$$

With $j=na$ all conditions of $\operatorname{Prec}(n,\kappa,a,l,j)$ hold ($n\notin\mathcal C$,
$\kappa\ne0$, $a,l\ge1$, and $l,a,j$ are admissible because they are nonzero), and the window
$|t-r(a,j)|<\epsilon_l$ holds for $t=n$. The order of choices matters: $l$ is fixed first, then
$a$ depending on $\epsilon_l$.

## Depends on

- [The precision relation](../../compiler/natural/precision/precision-relation.md)
- [The local parameter z on multiples of the generator](../../compiler/natural/precision/z-coordinate.md)
- [The precision constant is the six-contact constant](../../compiler/natural/precision/precision-height-constant-value.md)
- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)
- [The outer composition recipes](../../syntax/recipes/outer-recipes.md)
- [Point codes](../../model/point-codes.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)
- [Pole completeness](../../main/pole-completeness.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [The relation Close](close-relation.md)
- [Multiples of the generator approach the identity at both real places](real-accumulation.md)
- [The derivative of multiplication at a real place](real-derivative.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)

## Sources

- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
