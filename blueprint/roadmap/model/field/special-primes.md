---
article_id: af_cc78b20baec329eb2f10f686
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.prime_sqrt2Z, ZInQ.prime_genDZ, ZInQ.vS_formula_withTop
---

# The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$

1. $s$ is a prime element of $\mathbb Z[s]$, $2=s^2$, and $\mathbb Z[s]/(s)\cong\mathbb F_2$ via
   $a_0+a_1s\mapsto a_0\bmod2$. For $c_0,c_1\in\mathbb Q$ not both zero,
   $$v_s(c_0+c_1s)=\min\bigl(2v_2(c_0),\ 2v_2(c_1)+1\bigr),$$
   with $v_2$ the $2$-adic valuation on $\mathbb Q$ and $v_2(0)=+\infty$.
2. $d=75-53s$ is a prime element with $\operatorname N(d)=7$, and
   $\mathbb Z[s]/(d)\cong\mathbb F_7$ via $a_0+a_1s\mapsto a_0+3a_1\bmod7$. In this residue field
   $-1$ is not a square.
3. $\delta=3-s=\epsilon^4d$ with $\epsilon^4=17+12s$, so $\delta$ and $d$ are associates and
   $v_d=v_\delta$. Moreover $v_s(d)=v_s(\delta)=v_s(\epsilon)=0$, $v_d(s)=v_d(2)=0$, and
   $d$ is totally positive ($\sigma_\pm(d)=75\mp53\sqrt2>0$), as is $\delta$.

**Proof sketch.** An element whose norm is $\pm$ a rational prime is irreducible, hence prime
in the principal ideal domain $\mathbb Z[s]$; $\operatorname N(s)=-2$, $\operatorname N(d)=7$.
The residue maps are ring homomorphisms by the residue computations modulo seven (and
$s^2=2\equiv0$ modulo $2$), surjective, with kernels $(s)$ and $(d)$ since the quotients have
$|\operatorname N|$ elements. For the formula in (1), $v_s$ of a rational $c$ is $2v_2(c)$ and of
$cs$ is $2v_2(c)+1$; the two values have different parity, so the valuation of the sum is
their minimum. (3) is the identity $(75-53s)(17+12s)=3-s$, and $75^2=5625>5618=2\cdot53^2$.

## Depends on

- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](integers-pid.md)

## Proof depends on

- [Residue computations modulo seven](residue-checks.md)
- [Units of $\mathbb Z[\sqrt2]$](units.md)
- [Explicit identities in $K_0$](explicit-identities.md)

## Sources

- [First descent image](../../../sources/model-locators.md#first-descent-image)
- [Second descent image](../../../sources/model-locators.md#second-descent-image)
- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
