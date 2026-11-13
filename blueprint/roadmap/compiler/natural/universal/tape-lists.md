---
article_id: af_672888b0c762326f9d996138
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.cons, ZInQ.Compiler.Universal.uncons, ZInQ.Compiler.Universal.listCode, ZInQ.Compiler.Universal.listCode_bijective, ZInQ.Compiler.Universal.listGet_listSet_self, ZInQ.Compiler.Universal.listSet_listCode, ZInQ.Compiler.Universal.Represents
---

# Tape lists

Code finite lists of naturals by $\operatorname{nil}=0$ and
$\operatorname{cons}(h,t)=2^h(2t+1)$. Then:

1. $\operatorname{cons}$ is a bijection from $\mathbb N^2$ onto the positive naturals; for $x>0$
   the head $h$ is the number of halvings of $x$ until it is odd and the tail is
   $t=(x/2^h-1)/2$; moreover $t<x$ and $h<x$;
2. every natural number codes exactly one finite list;
3. for a list code $L$ and $i\in\mathbb N$, $\operatorname{get}(L,i)$ (the $i$-th entry, or $0$ if
   the list is shorter) and $\operatorname{set}(L,i,v)$ (the list with entry $i$ replaced by
   $v$, padded with zeros if it is shorter) are well defined, with
   $\operatorname{get}(\operatorname{set}(L,i,v),i)=v$ and
   $\operatorname{get}(\operatorname{set}(L,i,v),i')=\operatorname{get}(L,i')$ for $i'\ne i$.

A register file $\rho$ is *represented* by a list code $L$ when $\rho(i)=\operatorname{get}(L,i)$
for every $i$; absent entries are zero, so a file has many representing codes.

**Proof sketch.** Unique factorization $x=2^h\cdot\mathrm{odd}$ gives the bijection;
$2^h(2t+1)\ge2t+1>t$ and $2^h>h$. Lists are coded by recursion on length, and the decoding
terminates because tails decrease. The get/set equations are by induction on $i$.

## Depends on

None.

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
