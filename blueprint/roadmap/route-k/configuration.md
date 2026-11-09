---
article_id: af_5bf99da09fd2edaa97602a8b
declaration: structure
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Config, ZInQ.RouteK.oddClasses, ZInQ.RouteK.lam8, ZInQ.RouteK.mu8, ZInQ.RouteK.Config.lam, ZInQ.RouteK.Config.mu, ZInQ.RouteK.Config.prodClass, ZInQ.RouteK.Config.bit_symm_of_cls_one
---

# Configurations

For an odd class $c$ modulo $8$ put $\lambda(c)=[c\equiv3\pmod4]$ and
$\mu(c)=[c\equiv3,5\pmod8]$, as elements of $\mathbb F_2$.

A *configuration* $\mathcal C$ on a finite set $S$ of symbols (the "primes" of $\mathcal C$)
consists of a class $c_x\in\{1,3,5,7\}\subset\mathbb Z/8$ for every $x\in S$ and a bit
$[y/x]\in\mathbb F_2$ for every pair $x\ne y$ of elements of $S$, subject to reciprocity:
$$[x/y]+[y/x]=\lambda_x\lambda_y\qquad(x\ne y),$$
where $\lambda_x=\lambda(c_x)$ and $\mu_x=\mu(c_x)$. Bits $[x/x]$ on the diagonal play no role.
The *product class* of $\mathcal C$ is $c(\mathcal C)=\prod_{x\in S}c_x$ modulo $8$; it is again
odd. A symbol $r$ with $c_r=1$ is a *glue prime*; for it $\lambda_r=\mu_r=0$, so reciprocity
makes its bits symmetric, $[r/x]=[x/r]$.

The model is an odd squarefree $d>0$: its primes with their classes modulo $8$ and their
Legendre symbols form a configuration, by quadratic reciprocity
([the configuration of an odd number](prime-configuration.md)). Configurations that no number
realizes occur only as intermediate steps of the descent.

## Depends on

None.

## Sources

- [Configurations and the Selmer system](../../sources/route-k-locators.md#configurations-and-the-selmer-system)
