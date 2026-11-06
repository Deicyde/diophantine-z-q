---
article_id: af_89b843dffed2f563c786d16b
declaration: lemma
origin: cited
---

# List codes for the interpreter tape

Put $\operatorname{cons}(h,t)=2^h(2t+1)$, and code finite lists of naturals by
$\langle\,\rangle=0$ and $\langle h,L\rangle=\operatorname{cons}(h,\langle L\rangle)$. For a code $c$ and $i\in\mathbb N$
let $\operatorname{get}(c,i)$ be the $i$-th entry of the list coded by $c$, and $0$ if the list has
no $i$-th entry; let $\operatorname{set}(c,i,v)$ be the code of that list with its $i$-th entry
replaced by $v$, after padding the list with zero entries up to length $i+1$ if necessary.

1. $\operatorname{cons}$ is a bijection from $\mathbb N\times\mathbb N$ onto the positive integers, and every
   natural number is the code of exactly one finite list.
2. For $c\ge1$, halving $c$ while it is even terminates after $h=v_2(c)$ steps with the odd
   number $2t+1$, where $(h,t)$ is the unique pair with $c=\operatorname{cons}(h,t)$; and $t<c$.
3. $\operatorname{get}(\operatorname{set}(c,i,v),i)=v$ and $\operatorname{get}(\operatorname{set}(c,i,v),i')=\operatorname{get}(c,i')$
   for $i'\ne i$. So if $c$ represents registers $R$ (that is, $\operatorname{get}(c,i)=R_i$ for all
   $i$), then $\operatorname{set}(c,i,v)$ represents $R[i\mapsto v]$; absent entries read as zero.
4. The reversed-prefix procedure (move the first $i$ entries onto a reversed prefix code,
   padding with zeros past the end, replace the head, then move the prefix back) computes
   $\operatorname{set}(c,i,v)$, and the analogous walk computes $\operatorname{get}(c,i)$; each terminates,
   since the remaining code strictly decreases on the way out and the saved prefix strictly
   decreases on the way back.

**Proof sketch.** (1) Every positive integer is $2^h$ times a unique odd number $2t+1$; induct on
the code for lists, using $t<\operatorname{cons}(h,t)$. (2) Each halving of an even positive number
decreases it and preserves positivity. (3) Induction on $i$ along the list. (4) Induction on
$i$ with the invariant "reversed prefix followed by the remaining list is the current list".

## Depends on

None.

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
- [Machine artifacts](../../../../sources/compiler-translation-locators.md#machine-artifacts)
