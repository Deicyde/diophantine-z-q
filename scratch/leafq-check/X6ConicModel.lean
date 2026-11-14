import TailK

/-!
# leafq-check: `X6ConicModel` (LEAF?) — verbatim copy over leaf-fold4's chain

The Prop `HDec.X6Kummer.X6ConicModel` is copied verbatim (docstring and body) from `scratch/leaf-fold4/Leaves4.lean`
(def at line 75669), inside the sub-namespace `HDec.X6Kummer.LeafQCheckCopy` with the `open`s in force at its
location; what it depends on is imported from leaf-fold4's olean chain (`import TailK`, the same
constants as the flat file). `copy_iff` checks that the copy is the chain's Prop. Verdict, published
statement and decomposition: docs/research/leafq-check.md §2.6. Check: `scratch/leafq-check/chk.sh scratch/leafq-check/X6ConicModel.lean`.
-/

namespace HDec.X6Kummer

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

namespace LeafQCheckCopy

/-- **N2-L′ (leaf, new; the global form of `X6KummerModel`): `X₆ = X₀(6,1)` is the conic
`Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27 Z²)`, on `ℚ̄`-points of one witness.**

*Published statement* (Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979): `X₀(6,1) : x² + y² + 3 = 0`;
Elkies, ANTS-III, LNCS 1423 (1998), §3: `X*(6) = X₆/W` with coordinate `t`, `t = 0, 1, ∞` at the
CM points of discriminants `−24, −4, −3`, and `X₆ = X*(6)(√−t, √(3(t − 1)))`; locators
UNVERIFIED, no network). Put `X = √−t`, `Y = √(3(t−1))`, `Z = 1`: then `Y² + 3X² + 3 = 0`,
`t = −X²/Z²`, `W` acts by the sign changes, and `j = 16(t − 1)/27 = −16(X² + Z²)/(27 Z²)` is the
coordinate of R2fp (`j = 0, ∞, −16/27` at `−4, −3, −24`; a Möbius map is fixed by three values).
An isomorphism of `ℚ`-schemes `X₆ ≅ C` gives a bijection on `ℚ̄`-points commuting with
`Aut(ℚ̄/ℚ)`, compatible with the maps to `P¹`. Consistency checks (VERIFIED by computation in
`scratch/x6-kummer/conic_check.py`): the involutions `X ↦ −X`, `Y ↦ −Y`, `(X,Y) ↦ (−X,−Y)` fix
exactly the two points over `j = −16/27`, `0`, `∞` respectively (Riemann–Hurwitz for a
`(ℤ/2)²`-cover of `P¹` by a genus-0 curve); the residue fields there are `ℚ(√−3)`, `ℚ(i)`,
`ℚ(√−3)`, as González–Rotger Thm 5.12 (the bundle's `R5ptProps`) requires for `ℤ[√−6]` (`b = 0`,
`h = 2`), `ℤ[i]` (`b = 1`, `h = 1`, contains `ℚ(i)`), `ℤ[ζ₃]` (`b = 1`, `h = 1`, contains
`ℚ(√−3)`); `C` and Kurihara's conic both correspond to `(−1, −3)_ℚ`, ramified at `{3, ∞}`. The
fibre fields `ℚ(√−t, √(3(t−1)))` were checked against González–Rotger Thm 5.12 on all 24 rational
CM points of Elkies' table by rv-nocm §1.3 Part B. -/
def X6ConicModel : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ ∧ ConicModel X π₆

end LeafQCheckCopy

theorem LeafQCheckCopy.copy_iff : LeafQCheckCopy.X6ConicModel ↔ X6ConicModel := Iff.rfl

end HDec.X6Kummer
