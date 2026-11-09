---
article_id: af_986c5fd18351e100af5d830f
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.shift_choice, ZInQ.Mult.shift_choice'
---

# Choice of the shift at a selected prime

Let $M\ge1$ and $d_1,d_2\ge1$ be integers with $\gcd(d_1,d_2)=4$. Then there is an integer
$h>4M$ with
$$h\equiv0\pmod{\operatorname{lcm}(M,d_1)},\qquad h\equiv4M\pmod{d_2}.$$
In the application $M=M_0$, $4M=c_*$, and $d_1,d_2$ are the orders of the two reduced curve
groups at a selected prime; then $h\ne0$, $h\ne c_*$, $M_0\mid h$, $d_1\mid h$ and
$d_2\mid h-c_*$.

**Proof sketch.** The two congruences are compatible iff
$\gcd(\operatorname{lcm}(M,d_1),d_2)\mid4M$. Since $\operatorname{lcm}(M,d_1)\mid Md_1$,
$\gcd(\operatorname{lcm}(M,d_1),d_2)\mid\gcd(Md_1,d_2)\mid\gcd(Md_1,Md_2)=M\gcd(d_1,d_2)=4M$.
By the Chinese remainder theorem the solutions form a residue class modulo
$\operatorname{lcm}(\operatorname{lcm}(M,d_1),d_2)$, which contains integers larger than $4M$.

## Depends on

None.

## Sources

- [Choice of shifts](../../../sources/multiplication-locators.md#choice-of-shifts)
