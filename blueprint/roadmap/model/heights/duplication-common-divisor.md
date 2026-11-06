---
article_id: af_4e6dae43a04efa9a961a8460
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.duplication_common_divisor
---

# The common divisor of the duplication forms

Let $a,b\in\mathbb Z[s]$ be coprime and let $g$ be a greatest common divisor of $F_2(a,b)$ and
$G_2(a,b)$ (assume they are not both zero). Then $v_\pi(g)=0$ for every prime $\pi$ associate
to neither $s$ nor $\delta$, $v_s(g)\le6$ and $v_\delta(g)\le4$. Consequently
$$|\operatorname N(g)|\le2^6\cdot7^4=392^2 .$$

**Proof sketch.** It suffices to bound $v_\pi(F_2(a,b))$ whenever $\pi$ divides both forms.
*Primes $\pi\nmid2\delta$.* If $\pi\mid a$ then $\pi\mid a^2+\delta^2b^2$ forces $\pi\mid b$; similarly
$\pi\mid b$ forces $\pi\mid a$; and $\pi\mid a^2-\delta^2b^2$ together with
$\pi\mid a^2+\delta^2b^2$ gives $\pi\mid2a^2$. All contradict coprimality. *At $\delta$.* If
$\delta\nmid a$, $F_2\equiv a^4\not\equiv0$. If $\delta\mid a$, then $\delta\nmid b$ and with
$a=\delta a'$, $F_2=\delta^4(a'^2+b^2)^2$; since $-1$ is not a square modulo $\delta$ (residue field
$\mathbb F_7$), $\delta\nmid a'^2+b^2$, so $v_\delta(F_2)=4$. *At $s$.* If exactly one of $a,b$ is
divisible by $s$, $a^2+\delta^2b^2$ is prime to $s$ and $v_s(F_2)=0$. If neither is, the dyadic
valuation computation gives $v_s(a^2+\delta^2b^2)\in\{2,3\}$, so $v_s(F_2)\le6$. Finally
$|\operatorname N(s)|=2$, $|\operatorname N(\delta)|=7$ and $2^6\cdot7^4=153664=392^2$.

## Depends on

- [The duplication forms on $C$](duplication-forms.md)
- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](../field/integers-pid.md)

## Proof depends on

- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../field/special-primes.md)
- [A dyadic valuation computation](../field/dyadic-valuation.md)
- [Explicit identities in $K_0$](../field/explicit-identities.md)

## Sources

- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
