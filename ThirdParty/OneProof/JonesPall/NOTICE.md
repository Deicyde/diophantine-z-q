# Jones–Pall exact squarefree representation: source and change notice

## Scope

`ZInQKernel.Contrib.OneProof.JonesPall` imports the defining module
`ZInQKernel.Contrib.OneProof.TYZLemma29Mod2`, never `ZInQKernel.OneProof.Main`.
It exports `ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof` with exactly the
unchanged proposition `ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16`:

```lean
∀ n : ℕ, Squarefree n → n % 8 = 1 →
  ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + 16 * z ^ 2
```

There is no additional outer representation hypothesis, changed target, new
Lake dependency, or modified project/toolchain/Mathlib pin. This supplies the
single `hJP` argument, not the complete unconditional H10/Q theorem.

## Genuine three-square supplier

- Public source: https://github.com/facebookresearch/atlas-lean
- Immutable commit: `8860f7b55276b96e51df600021845dd5eb48f5ab`
- Original file: `MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean`
- Original source SHA-256: `a902763f2e8c6ca272f03774536d58b93c99f5843214288efe226f5e767da284`
- Source link: https://github.com/facebookresearch/atlas-lean/blob/8860f7b55276b96e51df600021845dd5eb48f5ab/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean
- The original copyright header and full upstream license, including its
  prefatory text, are preserved in the canonical provider. The shared
  `LegendreThreeSquares/LICENSE` SHA-256 is:
  `fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.

The contribution imports the **canonical common module**
`ZInQKernel.Contrib.OneProof.LegendreThreeSquares.Atlas`, published in draft
https://github.com/Deicyde/diophantine-z-q/pull/36 at immutable head
`47ca4df214d1402caa3de40c7d6f661567120fcd`. Its three shared files are carried
byte-identically at the same canonical paths until that dependency is on main:
`LegendreThreeSquares/Atlas.lean`, `LegendreThreeSquares/LICENSE`, and
`LegendreThreeSquares/NOTICE.md`.

`Representation.lean` fully qualifies that common module's Nat theorem. There
is no second Ankeny implementation or separate JonesPall.Atlas provider in the
final source tree. This draft depends on PR #36's shared provider; it does not
add or claim its hL3s entry theorem. The separate Legendre primary files and
published source are untouched. The superseded private namespace copy remains
reachable in historical commit `9edb3362593eeb1be4de6a7119c22f3d036c7e65`; the
follow-up deduplication does not erase or amend that history.

## New quaternion descent and transport

The new `Quaternion.lean`, `Descent.lean`, `Parity.lean`, and `Representation.lean`
use Mathlib's actual integral Hamilton quaternions, norm, conjugation,
coordinatewise divisibility, and sums-of-two-squares criterion. The descent
adapts the genuine Lagrange/Euler method in
`Mathlib/NumberTheory/SumFourSquares.lean` (Chris Hughes), at the project's
unchanged Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The dependency's complete Apache 2.0 license is preserved as `Mathlib.LICENSE`.

The argument is specialized to the exact squarefree target:

1. If n has no prime factor 3 modulo 4, Mathlib's two-square criterion gives
   the representation with z=0.
2. Otherwise choose a prime p dividing n, p=3 modulo 4. The genuine three-square
   theorem supplies an oriented representation. Squarefreeness proves its
   pure quaternion v is nonzero modulo p.
3. Balanced lifting gives a nonzero integral element of the left annihilator
   qv=0 modulo p, of norm kp with 1≤k<p. Minimality, left norm-two halving, and
   odd Euler remainder descent produce an actual quaternion q of norm p.
   Integrality, scalar coprimality, and zero-remainder cases are proved, not
   supplied as premises.
4. qv·conj(q)/p has integral coordinates and norm n. A kernel-checked finite
   residue lemma proves the mod-four parity switch; it is a statement about
   residue classes, not a finite verification of the unbounded target.
5. Exact division of the four-divisible coordinate yields the integer
   witnesses for x²+y²+16z², including all boundary cases of the stated target.

## Printed-source locator actually read

B. W. Jones and G. Pall, *Regular and semi-regular positive ternary quadratic
forms*, Acta Mathematica 70 (1939), pp.165–191, original journal scan:
https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5599-11511_2006_Article_BF02547347.pdf

The source PDF was opened, including the integral-quaternion definitions and
Theorems 2, 5, and 6. **Theorem 5**, printed p.177 (PDF p.13), is the equal-count
A/B representation statement for nonsquares. The direct representation result
is **Theorem 6**, printed pp.179–180 (PDF pp.15–16), whose first listed form is
(1,1,16). Short verbatim excerpt, mathematical typesetting linearized:

> Every positive integer of the form 8 n + 1 is represented in

This is an **AI-READ** source note, not a human reading; it changes no repository
ratings or human-reading flags. The new proof does not assume either printed
theorem as an axiom or additional hypothesis.

## Verification and contribution limits

Verification uses unchanged Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The exact exported constant, its fully
expanded integer-witness example, and axiom reports are checked separately.
Compiler/type/axiom/discharge results and independent review are reported in
the focused draft PR rather than inferred from source titles or finite tests.

This is AI-assisted formal-source reuse and a new exact proof. It introduces
no new axiom or kernel-check bypass, changes no existing repository file, and
makes no merge/landing or full-H10 completion claim.
