# cr3-mw report: Mordell–Weil for the congruent number curves over ℚ

## Proved (no sorry; axioms propext, Classical.choice, Quot.sound)

Namespace `ZInQ.RouteK.Rank`. Root module `ZInQKernel/RouteK/RankMW.lean`, imported from
`ZInQKernel.lean`. `lake build ZInQKernel` passes.

- `fg_points (d : ℕ) (hd : d ≠ 0) : AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point`
  (RankMW.lean), obtained from `AddCommGroup.fg_of_descent'` with Mathlib's naive height over ℚ,
  as in Model/Descent/MordellWeil.lean.
- `finiteIndex_two_points d hd : (nsmulAddMonoidHom 2).range.FiniteIndex` for `C_d(ℚ)`.
- `twoTorsion_card (d : ℕ) (hd : d ≠ 0) :
   Nat.card {P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point // 2 • P = 0} = 4`
  (RankMW/Torsion.lean). A form that is easier to use: `mwTwoTorsion_iff d hd P : 2 • P = 0 ↔
  P = 0 ∨ P = mwTwoTorsionPt d hd 0 _ ∨ P = mwTwoTorsionPt d hd d _ ∨ P = mwTwoTorsionPt d hd (-d) _`,
  where `mwTwoTorsionPt d hd e he = .some e 0 _`. `mwIsElliptic d hd` is the ellipticity of `C_d`.

### Ingredients (any field `K` unless stated)
- RankMW/PhiAdd.lean, **the two-isogeny `phi` of Kummer.lean is additive**: `mwPhi_add hb' P Q`,
  bundled as `mwPhiHom hb' : E_b →+ E_{b'}`. Kummer.lean only had `phi` as a function, and the
  index bound needs the dual isogeny to be a homomorphism, so this was the main new piece.
  Method: if P₁, P₂, P₃ = -(P₁+P₂) lie on y = ℓx + ν, then the φ(Pᵢ) lie on Y = LX + N with
  L = b/ν - ℓ, N = -ν - bℓ²/ν (`mwPhi_line`, an identity for one point), and ΣXᵢ = L² from
  Vieta (`mwPhi_sum_sq`). The tangent case is `mwPhi_tangent`, the line and tangent addition on
  E_{b'} is `mwAdd_of_line` / `mwDouble_of_line`, and the degenerate cases use `mwPhi_neg`,
  `mwPhi_add_tZero` (φ(P + (0,0)) = φ(P)) and `mwAdd_tZero_some` (explicit P + (0,0)).
- RankMW/Index.lean: `mwFiniteIndex_two_of_kummer hb' hb'' h h'`: if `Set.range (kummer b)` and
  `Set.range (kummer b')` are finite (b' = -4b, b'' = -4b'), then 2E_b has finite index. Uses
  `mwPhiHat = rescale ∘ φ_{b'}`, `mwKer_kummer_eq_range` (ker α_b = φ̂(E')),
  `mwKer_kummer'_le_comap` (ker α_{b'} ≤ φ̂⁻¹(2E)) and `relIndex_mul_index`.
- RankMW/Image.lean (over ℚ): `mwKummer_range_finite (c : ℤ) (hc : c ≠ 0)`: the image of
  `kummer (c : ℚ)` lies in the square classes of the integers m with |m| dividing |c|.
  `mwEven_padicValRat_x`: v_p(x) is even for p ∤ c. `mwSqc_eq_divisor`: a rational with even
  valuations away from B is, modulo squares, a signed divisor of B (squarefree part of num·den).

## Left / suggestions
- Only finiteness of [C_d(ℚ) : 2C_d(ℚ)] is proved, not its exact value.
- For RK9, the sibling task can combine `fg_points`, `twoTorsion_card` and the structure theorem for
  finitely generated abelian groups to get #C_d(ℚ)/2C_d(ℚ) = 2^(2 + rank).
- `mwPhiHom` and `mwPhiHat` are generic, so they also serve other curves y² = x³ + bx.
- I did not edit scripts/print_axioms.lean because the task names no lines in it. Suggested
  lines: `#print axioms ZInQ.RouteK.Rank.fg_points` and `#print axioms ZInQ.RouteK.Rank.twoTorsion_card`.

## Problems
None blocking. The linear_combination coefficients for the rational identities came from a
small sympy script that divides the cleared goal by the curve relations, after substituting
x₃ and b from Vieta's relations.
