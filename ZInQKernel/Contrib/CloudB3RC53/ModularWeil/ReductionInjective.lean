import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero

/-!
# A fragment of (R): reduction is injective on prime-to-`p` torsion at good reduction

`ModularWeil/FrobeniusTrace.lean` reduces the Frobenius trace dictionary at good reduction to the
reduction comparison of Tate modules (R), `TateReductionComparison`, whose first missing piece is:
at good reduction, reduction is injective on prime-to-`p` torsion (and bijective on it over an
algebraically closed field of characteristic zero).

This file proves that piece over any field `L` with a valuation subring `A`, for a Weierstrass
curve `W` with coefficients in `A` and good reduction (the reduced discriminant is nonzero), and
an integer `N` invertible in the residue field `k` of `A`:

* `reduceHom_injOn_torsion` (PROVED): `W(L)[N] → W̃(k)[N]` is injective;
* `eq_zero_of_reduceHom_eq_zero` (PROVED): the kernel of reduction has no nonzero `N`-torsion
  (no torsion prime to the residue characteristic);
* `reduceHom_mapsTo_torsion` and, for `L` algebraically closed of characteristic zero,
  `reduceHom_bijOn_torsion` (PROVED): reduction is a bijection `W(L)[N] → W̃(k)[N]`.

The proofs are the reduction homomorphism and its theorems from the vendored library
`ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT` (vendored from
`anthropics/fermats-last-theorem` at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, licence
Apache-2.0; see `Vendor/AnthropicFLT/LICENSE`, `NOTICE.upstream`, `ATTRIBUTION.upstream.md`):
`WeierstrassCurve.reduceHom`, the injectivity on torsion `reduceHom_injOn'` (an `N`-torsion point
has integral coordinates, so it reduces to the point at infinity only if it is the identity), and
the surjectivity on torsion
`WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero`.
These are library results used as infrastructure, not prints.

**What remains of (R).** To apply this inside `TateReductionComparison`, one needs: the valuation
subring of `\bar ℚ_p` attached to an extension `w` of the `p`-adic valuation; an integral model of
`E` over it (the minimal model over `ℤ_(p)`, good reduction at `p`); the identification of its
residue field with `\bar 𝔽_p` and of the reduced curve with `reducedCurveModP E p` base changed to
`\bar 𝔽_p`. With those, this file gives the isomorphism `E(\bar ℚ_p)[ℓⁿ] ≅ Ẽ(\bar 𝔽_p)[ℓⁿ]` for
`ℓ ≠ p`, hence on Tate modules; Galois-equivariance (arithmetic Frobenius acting as `x ↦ x^p` on
reduced coordinates, `IsArithmeticFrobeniusOnClosureQ`) is the other remaining part of (R).

**Classification.** PROVED (from the vendored library).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open WeierstrassCurve IsLocalRing

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)] {W : WeierstrassCurve A}

open P2MW.S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero in
/-- **Reduction is injective on prime-to-`p` torsion at good reduction** (PROVED; vendored
`reduceHom_injOn'`). -/
theorem reduceHom_injOn_torsion (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ}
    (hN : (N : ResidueField A) ≠ 0) :
    Set.InjOn (reduceHom hΔ) {P : (W.map A.subtype).toAffine.Point | N • P = 0} :=
  fun _ hP _ hQ h =>
    ChildL.reduceHom_injOn' hΔ hN hP hQ h

/-- **The kernel of reduction has no torsion prime to the residue characteristic** (PROVED). -/
theorem eq_zero_of_reduceHom_eq_zero (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ}
    (hN : (N : ResidueField A) ≠ 0) {P : (W.map A.subtype).toAffine.Point} (hP : N • P = 0)
    (h : reduceHom hΔ P = 0) : P = 0 :=
  reduceHom_injOn_torsion hΔ hN hP (show N • (0 : (W.map A.subtype).toAffine.Point) = 0 from
    nsmul_zero N) (by rw [h, map_zero])

/-- Reduction maps `N`-torsion to `N`-torsion. PROVED. -/
theorem reduceHom_mapsTo_torsion (hΔ : (W.map (residue A)).Δ ≠ 0) (N : ℕ) :
    Set.MapsTo (reduceHom hΔ) {P : (W.map A.subtype).toAffine.Point | N • P = 0}
      {Q : (W.map (residue A)).toAffine.Point | N • Q = 0} := fun P hP => by
  change N • reduceHom hΔ P = 0
  rw [← map_nsmul, show N • P = 0 from hP, map_zero]

/-- **Reduction is a bijection on prime-to-`p` torsion** over an algebraically closed field of
characteristic zero (PROVED; vendored injectivity and surjectivity). -/
theorem reduceHom_bijOn_torsion [IsAlgClosed L] [CharZero L] (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0) :
    Set.BijOn (reduceHom hΔ) {P : (W.map A.subtype).toAffine.Point | N • P = 0}
      {Q : (W.map (residue A)).toAffine.Point | N • Q = 0} :=
  ⟨reduceHom_mapsTo_torsion hΔ N, reduceHom_injOn_torsion hΔ hN, fun Q hQ => by
    obtain ⟨P, hP, h⟩ :=
      WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero A W hΔ hN Q hQ
    exact ⟨P, hP, h⟩⟩

end ZInQ.Contrib.CloudB3RC53.ModularWeil
