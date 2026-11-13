---
article_id: af_6ed95e961b9f8f38b7632e7a
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.natConfig, ZInQ.RouteK.primeCfg, ZInQ.RouteK.natClass, ZInQ.RouteK.SelmerCertified
---

# The configuration of an odd number and Selmer certificates

Let $(f_k)_{k\in K}$ be a finite family of distinct odd primes. Its *configuration* has the
symbols $K$, the classes $c_k=f_k\bmod 8$ and the bits $[f_a/f_b]$ (the residue bit of $f_a$
modulo $f_b$); reciprocity is quadratic reciprocity in residue bits. For an odd positive integer
$d$, the configuration $\mathcal C_d$ of $d$ is that of the primes dividing $d$.

For an integer $a$, the *class of $a$* in the coordinates of $d$ is
$(s(a),0,u)$ with $u_p=[p\mid a]$ for the primes $p\mid d$; when $a$ is a squarefree odd divisor
of $d$ it is the first coordinate of $a=(-1)^{s(a)}\prod_{p\mid a}p$.

A *Selmer certificate* for $(d,a)$, with $d$ odd and positive, is the statement that
$\Sigma(\mathcal C_d)$ has exactly $8$ solutions and that one of them has first coordinate the
class of $a$. Through Proposition 0 it says that $\dim_{\mathbb F_2}\mathrm{Sel}_2(C_d)=3$ and
that $a$ is a first Kummer coordinate of $\mathrm{Sel}_2(C_d)$, a certificate of Selmer type in
the sense of slot-k §1.2.

## Depends on

- [The Selmer system of a configuration](selmer-system.md)
- [Residue bits](residue-bits.md)

## Proof depends on

- [Quadratic reciprocity in residue bits](reciprocity-bits.md)

## Sources

- [Configurations and the Selmer system](../../sources/route-k-locators.md#configurations-and-the-selmer-system)
- [Certificates and the descent lemma](../../sources/route-k-locators.md#certificates-and-the-descent-lemma)
