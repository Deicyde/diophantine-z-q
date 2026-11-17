# h33-from-hgz (fleet note)

**Verdict: negative. `hGZ : GrossZagierAlgOptCd` does not imply `h33 : TYZSplit.TYZThm33`, even at the instances
`frozenTarget` uses.** Count change 0: no contribution file, no fold, no new leaf.

Why (docs/research/h33-from-hgz.md §2):
* For n ≡ 5 the field `K_n` has discriminant −4n, which is outside `hGZ`'s odd-discriminant scope. This is
  Lean-checked in `scratch/h33-from-hgz/Scope.lean`.
* `h33` carries the central value `ℓ(d₁)` of `L(C_{d₁}, s)`, through `L'(A_{d₀},1) L(A_{d₁},1) = L'(A_{K_n},χ,1)`.
  The trivial-character GZ for `C_{d₀}` with a Heegner discriminant never produces that L-function: a common prime
  breaks the Heegner hypothesis (Lean-checked).
* `hGZ`'s Heegner points live on `X₀(N_{E'})` over an auxiliary K and are unrelated to TYZ's `z_n` on `X₀(32)`.
* Proportionality needs Kolyvagin, and the first clause needs Tunnell–Saito.

TYZ's own proof (L1865–2040) uses YZZ's GZ with a genus character (explicit form, TYZ Thm EGZ, deduction omitted),
Kolyvagin, and Tunnell–Saito.

Recommendation: fold h33-dict's printed-form leaf `H33Dict.TYZThm33Printed` (origin/wip/h33-dict) in place of `h33`.
That changes GLUE → LEAF (printed form) with the count unchanged. Do not split it into YZZ+Kolyvagin+Saito–Tunnell:
that gives three leaves, and the YZZ explicit formula is not statable over genuine definitions today.

Compiles: `scratch/h33-from-hgz/Scope.lean` (Mathlib only, exit 0). Nothing under ZInQKernel/ was changed.
