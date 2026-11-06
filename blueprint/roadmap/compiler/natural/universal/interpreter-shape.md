---
article_id: af_a945a7f11fab24d207628760
declaration: theorem
origin: cited
---

# Shape of the universal interpreter

The universal interpreter is valid for $204$ registers and has $m=1{,}399$ instructions, of
which $s=1{,}022$ are sub instructions and $376$ are add instructions, its final
instruction being the only halt; it has $k=2$ inputs. Consequently its packed-history
construction has $2k+9+41r+10m+31s=54{,}049$ explicit variables (the two inputs included),
$2+3m+12r+9s=15{,}845$ power calls and variable count
$54{,}049+79\cdot15{,}845=1{,}305{,}804$; it has $1{,}603$ masks, $1{,}226$ bitAnd macros,
$3{,}678$ orthogonal macros and $5{,}281$ binomial macros.

This is a closed decidable statement about the explicit program, followed by integer
arithmetic.

## Depends on

- [The universal interpreter](universal-interpreter.md)
- [The packed-history construction](../packed/packed-compiler.md)

## Proof depends on

- [Variable and gadget counts of the packed construction](../packed/packed-counts.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
