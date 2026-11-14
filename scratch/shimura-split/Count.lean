import ZInQKernel.HDecomp.QM.Leaves

/-!
# shimura-split, Part 3: `R5fpCount` (row r5count) from González–Rotger's count on the points of `X₆`

`R5fpCount` counts isomorphism classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R`. González–Rotger
Prop. 5.6 counts CM points by `R` on the curve `X₀(6,1)`. The two agree through the moduli interpretation
of `X₆` (`X6Props`: `Ψ : X(ℚ̄) ≃ {QM pairs over ℚ̄}/≅`). This file states the count on the points of one
coarse witness (the canonical model, as `CanonicalCoarseX6`/`GonzalezRotgerX6` do for the other clauses) and
proves the row from it.
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF-form (González–Rotger Prop. 5.6 on the points of the canonical `X₆ = X₀(6,1)`).**

*Published statement* (González–Rotger, J. Math. Soc. Japan 58 (2006), Prop. 5.6, p. 943, read by the
locator audit in arXiv v1/v2 and the journal): for an order `R` of conductor prime to `DN` in an imaginary
quadratic field `k` that embeds optimally in the Eichler order of level `N` of the quaternion algebra of
discriminant `D`, the number of CM points by `R` on `X₀(D,N)` is `#CM(R) = 2^{#{p | D(R)N(R)}} h(R)`.
At `D = 6`, `N = 1`: `D(R)` is the product of the primes `p | 6` inert in `k` (rv-nocm §3.1), so
`#CM(R) = 2^{b(k)} h(R)` with `b(k) = inertCount6 k` and `h(R) = #Pic(R)`.

*Lean form*: some witness `(Y, Φ, X, Ψ, fY)` of the clause lists `R1fpProps`, `X6Props` (the canonical models
`Y₃`, `X₆` with the moduli interpretation of `X₆(ℚ̄)`) has, for every such `R` occurring as some
`End_𝒪(A)`, exactly `2^{b(k)} #Pic(R)` points `x ∈ X(ℚ̄)` whose QM pair has `End_𝒪(A) ≅ R` ("CM by `R`").

*Why faithful*: the printed count specialized to `(D, N) = (6, 1)`; "CM point by `R`" is a point whose QM pair
has `End_𝒪(A) = com ι ≅ R`. The hypotheses "conductor prime to 6" and "`R` occurs" are the printed ones
(optimal embedding). Lemma QP (polarizations) as for `R1fp`. Locators: the audit read Prop. 5.6. -/
def GonzalezRotgerCountX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
        (∃ P : QMPair Qbar, Nonempty (com P.q ≃+* R)) →
          Nat.card {x : fieldPt Qbar ⟶ X //
              ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ Nonempty (com P.q ≃+* R)} =
            2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

/-- **Row r5count from the count on points** (transport through the moduli bijection `Ψ`). -/
theorem r5fpCount_of_points (h : GonzalezRotgerCountX6) : R5fpCount := by
  obtain ⟨Y, Φ, X, Ψ, fY, -, -, hc⟩ := h
  intro k _ _ _ hk R hR hcond hocc
  rw [← hc k hk R hR hcond hocc]
  exact Nat.card_congr (Equiv.subtypeEquiv Ψ.symm (fun c => by
    constructor
    · rintro ⟨P, hP, hR'⟩; exact ⟨P, by rw [Equiv.apply_symm_apply]; exact hP.symm, hR'⟩
    · rintro ⟨P, hP, hR'⟩; exact ⟨P, by rw [Equiv.apply_symm_apply] at hP; exact hP.symm, hR'⟩))

/-- Conversely, the row and any witness give the count on its points (so the leaf-form is equivalent to the
row given `CanonicalModelY3`-type witnesses). -/
theorem points_of_r5fpCount (h : R5fpCount) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} (h1 : R1fpProps Y Φ) (h6 : X6Props Y Φ X Ψ fY) : GonzalezRotgerCountX6 := by
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, fun k _ _ _ hk R hR hcond hocc => ?_⟩
  rw [← h k hk R hR hcond hocc]
  exact Nat.card_congr (Equiv.subtypeEquiv Ψ (fun x => by
    constructor
    · rintro ⟨P, hP, hR'⟩; exact ⟨P, hP.symm, hR'⟩
    · rintro ⟨P, hP, hR'⟩; exact ⟨P, hP.symm, hR'⟩))

end ShimuraSplit

#print axioms ShimuraSplit.r5fpCount_of_points
#print axioms ShimuraSplit.points_of_r5fpCount
