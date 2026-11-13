# pi0-x6 results log

Task: Q4 of docs/research/rv-blueprints.md, `π₀(X₆) = 1` as glue. Target Lean clause:
`LeafAdopt.R1pi0Props X := GeometricallyConnected X.hom` (scratch/h-decomposition/Leaves.lean
L18636), inside the bundle `LeafAdopt.R1R2fpRep`.

## Findings

F1 (VERIFIED, read) rv-blueprints Q4 sketch, step "two components of degree 2 would each be
ramified over all three values; impossible since a quadratic cover is branched at an even number
of points": parity (Riemann–Hurwitz `2g−2 = −4 + B`, `B` even) only forbids exactly three branch
points. The sketch needs "`π₆` has no branch values outside `{0, ∞, −16/27}`" (every `ℚ̄`-fibre
outside the three values has 4 points). No clause of `R1R2fpRep` gives this: `R2X6PropsIff`
fixes the fibres (twist orbits) and the CM clauses at the three values only; `R5fpCount`
counts CM points by orders of conductor prime to 6. So the sketch, as written, is NOT glue from
the bundle. It becomes correct with one more clause (fixed points of nontrivial `W`-elements lie
over the three values: Baba–Granath 2008 §3.1 elliptic-order table, signature `(0;2,4,6)`, via
the uniformization; or Ogg 1983 fixed points of Atkin–Lehner involutions, UNVERIFIED locator).

F2 (argument checked here; SPECULATIVE until reviewed) A different argument needs NO branch
information: Galois action on the geometric components. Inputs:
 (a) `R5ptProps` (in the bundle) at `k = ℚ(i)`, `R = ℤ[i]` (2 ramified, 3 inert: `b = 1`, `h = 1`):
     every `ℚ̄`-point over `0` has residue field `ℚ(i)`; at `k = ℚ(√−3)`, `R = ℤ[ζ₃]` (2 inert,
     3 ramified: `b = 1`, `h = 1`): every point over `∞` has residue field `ℚ(√−3)`.
 (b) `R5fpCount` (in the bundle) at `ℤ[i]`: exactly `2^1·1 = 2` points over `0`.
 (c) "CM by `ℤ[i]`" in the sense `com ≅ ℤ[i]` at the points over `0` (and `com ≅ ℤ[ζ₃]` over `∞`):
     the bundle's `HasCM4` only says `com ∋ φ, φ² = −1`. Either a textbook leaf (`com` is `ℤ` or an
     order in an imaginary quadratic field: Albert/Shimura, h-trust A9 dichotomy) or a restated R2
     CM clause with `Nonempty (com P.q ≃+* ℤ[i])` (the printed meaning of "CM point by `ℤ[i]`").
 (d) algebraic geometry over `ℚ̄` (Mathlib lacks it): every connected component of `X_ℚ̄` contains
     a `ℚ̄`-point over `0` and one over `∞` (components are smooth proper irreducible curves; `π₆`
     is nonconstant on each because fibres are finite twist orbits, `Aut(𝒪)/Inn(𝒪^×) ≅ W` finite;
     proper image is all of `P¹`; Nullstellensatz); `Aut(ℚ̄/ℚ)` permutes components compatibly
     with its action on `X(ℚ̄)`; `X_ℚ̄` connected ⇒ `GeometricallyConnected X.hom`
     (Stacks, Varieties, "geometrically connected" ⇔ connected over `k̄`; UNVERIFIED tag).
 Proof: components ≤ #(fibre over 0) = 2. If two, `C₁ ∋ x₁`, `C₂ ∋ x₂`. Pick `y ∈ C₁` over `∞` and
 `σ` with `σ(√−3) = √−3`, `σ(i) = −i`. Then `σy = y` (residue field `ℚ(√−3)`), `σx₁ ≠ x₁`
 (residue field `ℚ(i)`), so `σx₁ = x₂`. `σ` maps `C₁ ∋ y, x₁` to the component of `σy = y` and of
 `σx₁ = x₂`: `C₁ = C₂`. Contradiction.

## Lean (scratch/pi0-x6/)

(entries below as compiled)
