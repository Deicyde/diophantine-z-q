---
article_id: af_87fb050a762911fe35006d01
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.packed_counts
---

# Variable and gadget counts of the packed construction

Let $p$ be valid for $r$ registers with $m$ instructions, of which $s$ are sub
instructions, and $1\le k\le r$. The packed-history construction of $p$ creates

- $m+r$ mask macros, $r+s$ bitAnd macros, $3(r+s)$ orthogonal macros, $m+4r+3s$ binomial
  macros, $m+4r+3s$ odd gadgets and $2+k+r+2(m+4r+3s)$ strict-inequality gadgets ($2+k+r$
  outside the binomials and two in each binomial);
- $2+3(m+4r+3s)=2+3m+12r+9s$ power calls, each with a private block of $79$ variables;
- $2k+9+41r+10m+31s$ explicit variables, the $k$ inputs included.

Hence the compiled circuit $\mathcal C_{p,k}$ has variable count
$$V=(2k+9+41r+10m+31s)+79\,(2+3m+12r+9s).$$
These counts are independent of the order of the instructions and of the jump targets.
The numbers of addition and multiplication nodes depend on hash-consing and on the
targets, and are not given in closed form here.

**Proof sketch.** Count the allocations of each step of the construction: seven fresh
variables $q,\dots,D$, $2r$ for $R_j,N_j$, $m$ for $S_i$, $2s$ for $V_i,W_i$; each lt, divides and
odd gadget takes one variable and each congruent two (only lt and odd occur outside the
power template); a binomial takes $5$ fresh variables, three power calls and two lt
gadgets; a mask or orthogonal macro takes one fresh variable, one binomial and one odd
gadget; a bitAnd takes two fresh variables and three orthogonals. Summing:
$k+7+2r+m+2s+(2+k+r)+2(m+4r+3s)+5(m+4r+3s)+(m+r)+3(r+s)+(m+4r+3s)+2(r+s)
=2k+9+41r+10m+31s$, and the power calls are the two of item 1 plus three per binomial.

## Depends on

- [The packed-history construction](packed-compiler.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Compiler source](../../../../sources/compiler-natural-locators.md#compiler-source)
