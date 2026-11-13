---
article_id: af_88b2d6278b5909f1494d674d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Syntax.ev_callPoly, ZInQ.Syntax.ExPoly.exists_blockUpdate_call_iff
---

# Evaluation of a template call

Let $\tau$ be a template or recipe with $p$ parameters, $v$ variables and $m=v-p$
witnesses, all of whose variables have index below $v$. Let $g_0,\dots,g_{p-1}$ be
polynomials, $w\in\mathbb N$ and $x:\mathbb N\to\mathbb Q$. Then
$$\tau[g;w]\,(x)=[\![\tau]\!]\,(g_0(x),\dots,g_{p-1}(x),x_w,x_{w+1},\dots,x_{w+m-1}).$$
Consequently, if none of the variables $X_w,\dots,X_{w+m-1}$ occurs in any $g_i$, then for
every assignment $x$ of the remaining variables
$$\bigl(\exists\,y_0,\dots,y_{m-1}\in\mathbb Q:\ \tau[g;w]\,(x[X_{w+j}\mapsto y_j])=0\bigr)
\iff\mathrm{Rel}_\tau(g_0(x),\dots,g_{p-1}(x)).$$

**Proof sketch.** Evaluation commutes with the substitution homomorphism: the value of
$\tau[g;w]$ at $x$ is the value of $[\![\tau]\!]$ at the assignment $i\mapsto g_i(x)$ for $i<p$ and
$i\mapsto x_{w+i-p}$ for $i\ge p$, and only $i<v$ matters. If the block variables do not occur
in the $g_i$, changing $x$ on the block leaves every $g_i(x)$ unchanged, and the block
values range over all of $\mathbb Q^m$; this is the existential statement.

## Depends on

- [Semantics of templates and recipes](../template-semantics.md)

## Sources

- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
