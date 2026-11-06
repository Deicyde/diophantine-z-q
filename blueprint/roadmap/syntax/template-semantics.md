---
article_id: af_dc5fe0d33182c9e924e487d9
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.Template.denote, ZInQ.Syntax.Recipe.denote, ZInQ.Syntax.ExPoly.Rel
---

# Semantics of templates and recipes

Polynomials live in $\mathbb Z[X_i : i\in\mathbb N]$ and every variable ranges over
$\mathbb Q$. A rational assignment is a map $x:\mathbb N\to\mathbb Q$, and $f(x)$ is the
value of $f$ at it.

**Scalar nodes.** A node list $n_0,\dots,n_{k-1}$ is a finite list in which every node
refers only to earlier nodes. A node is one of:

- $\mathrm{const}\ c$ with $c\in\mathbb Z$;
- $\mathrm{var}\ i$ with $i\in\mathbb N$ a local variable;
- $\mathrm{add}\ j\ j'$ or $\mathrm{mul}\ j\ j'$ with $j,j'$ earlier nodes;
- $\mathrm{call}\ \tau\ (a_0,\dots,a_{p-1})\ w$: a call of an earlier template $\tau$ with
  $p$ parameters, parameter nodes $a_i$ and witness start $w\in\mathbb N$;
- $\mathrm{fixed}\ e$ with $e$ a fixed integer expression;
- $\mathrm{psi}\ e\ (a_0,a_1,a_2,a_3)\ c$ with $e$ a fixed integer expression and
  $c\in\{0,1\}$;
- $\mathrm{guard}\ e\ (a_1,\dots,a_{15})$ with $e$ a fixed integer expression and fifteen
  coordinate nodes in point-major order.

**Templates.** A template $\tau=(p,v,n_0,\dots,n_{k-1},\mathrm{root})$ has parameter count
$p\le v$ and variable count $v$; its local variables $0,\dots,p-1$ are parameters and
$p,\dots,v-1$ are its $m=v-p$ witnesses. Node values are polynomials:
$[\![\mathrm{const}\ c]\!]=c$, $[\![\mathrm{var}\ i]\!]=X_i$, $[\![\mathrm{add}\ j\ j']\!]=[\![n_j]\!]+[\![n_{j'}]\!]$,
$[\![\mathrm{mul}\ j\ j']\!]=[\![n_j]\!][\![n_{j'}]\!]$, $[\![\mathrm{fixed}\ e]\!]$ is the constant
$\mathrm{val}(e)$, $[\![\mathrm{psi}\ e\ a\ c]\!]=\Psi_{\mathrm{val}(e),c}([\![n_{a_0}]\!],\dots,[\![n_{a_3}]\!])$,
$[\![\mathrm{guard}\ e\ a]\!]=G_{\mathrm{val}(e)}([\![n_{a_1}]\!],\dots,[\![n_{a_{15}}]\!])$ and
$[\![\mathrm{call}\ \tau'\ a\ w]\!]=\tau'[[\![n_{a_0}]\!],\dots,[\![n_{a_{p'-1}}]\!];w]$. The polynomial of
$\tau$ is $[\![\tau]\!]=[\![n_{\mathrm{root}}]\!]$.

**Calls.** For a template or recipe $\tau$ with $p$ parameters, polynomials
$g_0,\dots,g_{p-1}$ and $w\in\mathbb N$, the call $\tau[g_0,\dots,g_{p-1};w]$ is the image of
$[\![\tau]\!]$ under the ring homomorphism with $X_i\mapsto g_i$ for $i<p$ and
$X_i\mapsto X_{w+i-p}$ for $i\ge p$. Thus witness $p+j$ of the callee becomes the caller's
variable $X_{w+j}$.

**Relations.** For $a\in\mathbb Q^p$, $\mathrm{Rel}_\tau(a)$ holds when there are
$y_0,\dots,y_{m-1}\in\mathbb Q$ with $[\![\tau]\!]\,(a_0,\dots,a_{p-1},y_0,\dots,y_{m-1})=0$ (variables of index
at least $v$ set to $0$).

**Recipes.** A recipe $\rho$ has parameter count $p$, variable count $v$ and a list of
constraint polynomials $c_1,\dots,c_k$; its polynomial is $[\![\rho]\!]=\sum_i c_i^2$ for a
sum-of-squares recipe or a model-evaluation recipe and $[\![\rho]\!]=\prod_i c_i$ for a
product recipe (empty sum $0$, empty product $1$). Calls and relations of recipes are as for
templates.

- A *composition recipe* lists calls $(\kappa_i,(j_{i,0},\dots,j_{i,p_i-1}),w_i)$, where
  $\kappa_i$ is a template or an earlier recipe with $p_i$ parameters; its constraints are
  $c_i=\kappa_i[X_{j_{i,0}},\dots,X_{j_{i,p_i-1}};w_i]$. It also records ranges of fresh
  variables, which add no constraint.
- A *model-evaluation recipe* records generator indices $g_0,g_1,g_2$, source variable rows
  $(r,s)$ with a point reference $r$ and a natural start $s$ or none, constant definitions
  $(\sigma,r,s)$ with a scalar template $\sigma$, operations $(0,a,b,o,s)$, $(1,a,b,o,s)$
  and $(2,a,b,c,o,s)$, and a root equality $(r,r')$, together with operation templates
  $\nu$ (natural), $\alpha$ (raw addition), $\mu$ (multiplication) and possibly a power
  recipe $\pi$. Writing $\mathrm{ref}(r)$ for the five polynomials of a point reference and
  juxtaposing references for the concatenated coordinate lists, its constraints are, in this
  order: the three generator constraints $8X_{g_0}-1641$, $4X_{g_1}+15465$,
  $32X_{g_2}-87483$; $\nu[\mathrm{ref}(r);s]$ for each row with a natural start $s$;
  $\sigma[\mathrm{ref}(-2)\,\mathrm{ref}(r);s]$ for each constant definition;
  $\alpha[\mathrm{ref}(a)\,\mathrm{ref}(b)\,\mathrm{ref}(o);s]$,
  $\mu[\mathrm{ref}(a)\,\mathrm{ref}(b)\,\mathrm{ref}(o);s]$ and
  $\pi[\mathrm{ref}(a)\,\mathrm{ref}(b)\,\mathrm{ref}(c)\,\mathrm{ref}(o);s]$ for the operations of kinds $0$, $1$ and $2$;
  and the five differences $\mathrm{ref}(r)_i-\mathrm{ref}(r')_i$.

The order of summands does not change the polynomial; the order listed follows the
specification's description of model recipes. Source node numbers, source-node point
lists, names, metadata and provenance strings carry no constraints.

This is a definition. The denotation of a node list is computed by one pass in stored
order, keeping the polynomial of every node; a call refers to an earlier template, so the
library is denoted in its stored order. The values $\mathrm{val}(e)$, $\Psi_{n,c}$ and $G_T$ are
used only as symbols in all later reasoning; in particular $\mathrm{val}(e)$ is never
evaluated for the astronomical constants.

## Depends on

- [Fixed integer expressions](constants/fixed-integer-expressions.md)
- [Normalized division polynomials and their components](division-polynomials.md)
- [The finite false-triple product](constants/guard-product.md)
- [Point references](language/point-references.md)

## Sources

- [Appendix C.1](../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Appendix C.2](../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Section 2.1](../../sources/syntax-locators.md#section-21-literal-operations)
- [Saved specification](../../sources/syntax-locators.md#saved-specification)
