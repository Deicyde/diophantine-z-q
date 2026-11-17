# gr-isogdeg log

Base: wip/gr-isogdeg at 73ac1620 (= wip/r3-residual), merged origin/main (ff558bedd).

## Plan
- New leaf `GaudronRemondThm14AnDeg`: GaudronRemondThm14An with `isogDeg φ` (#ker(K̄)) replaced by
  `finDeg φ := φ.left.finrank (genericPoint B.X.left)` (Mathlib's `Scheme.Hom.finrank`, the rank of
  φ_*O at the generic point = [K(A):K(B)], meaningful without flatness since the stalk is a field).
- Glue: `isogDeg φ ≤ finDeg φ` for every isogeny, any characteristic (#ker(K̄) = separable degree ≤ degree):
  translates ξ·P of a geometric generic point ξ : Spec Ω → A by kernel points P are distinct Ω-points over
  φ∘ξ; those inject into ring maps Γ(φ⁻¹U) → Ω over Γ(U) → Ω, counted by `card_algHom_le_finrank`.

## Results
- Ring.lean: `card_ringHom_le_rankAtStalk` (R domain, S finite, ψ₀ injective, p = ⊥): compiles (VERIFIED).
- T0.lean: `Scheme.Hom.finrank` unfolds by `rfl` from a non-module file (body visible) (VERIFIED, after fixing
  the test statement).
