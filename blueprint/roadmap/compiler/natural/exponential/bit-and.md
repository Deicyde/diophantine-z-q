---
article_id: af_c2ec65ae8073ac7962f263e9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.bitAnd_gadget_iff, ZInQ.bitAnd_macro_iff
---

# The bitwise AND gadget

For natural numbers $z,x,y$ the following are equivalent:

1. there are natural numbers $a,b$ with $x=z+a$, $y=z+b$ and
   $z\mathbin{\mathrm{AND}}a=z\mathbin{\mathrm{AND}}b=a\mathbin{\mathrm{AND}}b=0$;
2. $z=x\mathbin{\mathrm{AND}}y$.

In the compiler, each of the three disjointness conditions is the orthogonality macro
($\binom{p+q}p$ odd, through the binomial-digit gadget and an odd-witness equation), and
the witnesses are introduced in the order $a,b$ (`and_left_only`, `and_right_only`).

**Proof sketch.** (1)$\Rightarrow$(2): disjointness makes the additions carry-free, so
$x=z\mathbin{\mathrm{OR}}a$ and $y=z\mathbin{\mathrm{OR}}b$, and with $z,a,b$ pairwise disjoint,
$(z\mathbin{\mathrm{OR}}a)\mathbin{\mathrm{AND}}(z\mathbin{\mathrm{OR}}b)=z$. (2)$\Rightarrow$(1): take
$a=x-z$ and $b=y-z$, the bit differences $x\mathbin{\mathrm{AND\,NOT}}y$ and
$y\mathbin{\mathrm{AND\,NOT}}x$; they are disjoint from $z$ and from each other.

## Depends on

None.

## Sources

- [Section 10.2 binomial and bits](../../../../sources/compiler-natural-locators.md#section-102-binomial-and-bits)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
