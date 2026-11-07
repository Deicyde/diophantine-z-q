---
article_id: af_56d6e8346eaa6e4b5aa332d8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.model_majorant, ZInQ.Size.composition_majorant
---

# Recipes satisfy the height majorant

Let $B\ge2^{20}$.

1. Let $\rho$ be a model-evaluation recipe with at most $B$ constraints, and suppose every
   callee $\kappa$ occurring in its calls satisfies $\mathrm{Maj}_B(h_\kappa,[\![\kappa]\!])$ with
   $h_\kappa\ge1$. Then $\mathrm{Maj}_B\bigl(\max(4,\max_\kappa(h_\kappa+3))+2,\ [\![\rho]\!]\bigr)$.
2. Let $\rho$ be a composition recipe with $m$ calls, $1\le m\le B$, whose callees satisfy
   $\mathrm{Maj}_B(h_i,[\![\kappa_i]\!])$. Then $\mathrm{Maj}_B(\max_ih_i+2,[\![\rho]\!])$ if $\rho$ is a sum of
   squares and $\mathrm{Maj}_B(\max_ih_i+1,[\![\rho]\!])$ if it is a product.

**Proof sketch.** (1) The constraints are the three generator equations
$8X_{g_0}-1641$, $4X_{g_1}+15465$, $32X_{g_2}-87483$, the calls, and the five root differences.
Every point reference is a variable, a constant $0$, $1$ or $-145$, or the negative of a
variable, so each argument polynomial has degree at most $1$ and norm at most $145$, and
satisfies $\mathrm{Maj}_B(2,\cdot)$. A call is a substitution of such arguments (and fresh
variables) into $[\![\kappa]\!]$, so it satisfies $\mathrm{Maj}_B(h_\kappa+3,\cdot)$ by rule (2). The
generator equations and root differences have degree at most $1$ and norm at most
$87515$, so they satisfy $\mathrm{Maj}_B(4,\cdot)$. By monotonicity every constraint satisfies
the majorant at $\max(4,\max_\kappa(h_\kappa+3))$, and rule (5) for the sum of at most $B$ squares
adds two. (2) The arguments of every call are coordinate variables, so each constraint is a
renaming of $[\![\kappa_i]\!]$ followed by moving witnesses to fresh variables, again a renaming:
rule (4) keeps $h_i$; then rule (5) or rule (6).

The manuscript calls the renaming case the reason why composition calls retain the
callee's height, and charges the model wrappers the safe height four.

## Depends on

- [Syntax heights](syntax-height.md)
- [Semantics of templates and recipes](../../syntax/template-semantics.md)

## Proof depends on

- [Closure rules for the height majorant](majorant-rules.md)
- [Point references](../../syntax/language/point-references.md)

## Sources

- [Section 12.1 syntax heights](../../../sources/size-locators.md#section-121-syntax-heights)
- [Section 12.1 checked facts](../../../sources/size-locators.md#section-121-checked-facts)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
