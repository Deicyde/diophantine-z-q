---
article_id: af_ac4bae90b32cf2c391e77669
---

# Exact precision computation and polynomial compilation

The ordinary-value argument needs one exact computation: from five integers
$(n,\kappa,a,l,j)$ it must decide whether $r(a,j)$ approximates $n$ to within $\epsilon_l$ and
whether $\epsilon_l$ is smaller than an explicit, astronomically small power of four. This
chapter turns that computation into rational point-code constraints in two stages. The fixed
constants are never evaluated: they enter only through their defining expressions and through
capped arithmetic.

First, the computation is compiled into a natural-number polynomial. A fixed universal halting
polynomial, obtained by packing finite runs of the universal interpreter into base-$B$ integers
and expressing the bit and power operations with the alpha and power formulas, is specialized
at the code $c_3$ of a wrapper around the precision machine. The result is the natural
precision polynomial $C$, with $1\,305\,811$ natural variables, the first five being inputs;
equation (C.4) states that it has a natural zero over $\mathbf c\in\mathbb N^5$ exactly when the
precision predicate accepts $\mathbf c$.

- [The natural polynomial and the power interface](natural/README.md)

Second, the natural polynomial is translated into the rational point-code model: each natural
variable becomes a code typed by the natural-code predicate and each arithmetic node a template
call, so that the precision recipe has rational witnesses exactly at the codes of the natural
zeros.

- [Translation to rational point codes](translation/README.md)
