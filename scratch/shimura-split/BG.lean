import ZInQKernel.Contrib.Mobius.ImagePlane

/-!
# shimura-split, Part 5: the surjectivity clause of `BabaGranathX6` is a theorem

qm-glue's leaf-form `BabaGranathX6` asks for `π₆ : X₆ → P¹` with the fibre and CM clauses of
`R2X6PropsIff` **and** `π₆` onto `P¹(ℚ̄)`. The second clause follows from the first: the fibres of `π₆` on
`ℚ̄`-points are the `Aut(𝒪)`-twist classes, which are finite (`Aut(𝒪)` is finite modulo inner automorphisms
by units, the kernel's `Pin.autOInnerFinite`, and inner twists are isomorphic, `Pin.conjUnitIso`), and a map
with finite fibres from a proper smooth curve over `ℚ` with a `ℚ̄`-point to `P¹` is onto `P¹(ℚ̄)` (the
kernel's `Pin.curveFacts.2 : CurveSurj`, proved by image-plane).
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.Pin

/-- **Finite twist classes of QM pairs over `ℚ̄`.** -/
theorem pairTwistClass_finite (P : QMPair Qbar) :
    {c : Quotient (pairSetoid Qbar) | ∃ Q : QMPair Qbar, c = Quotient.mk _ Q ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}.Finite := by
  obtain ⟨T, hTfin, hTα⟩ := autOInnerFinite
  refine (hTfin.image fun t => (Quotient.mk (pairSetoid Qbar) ⟨P.A, P.surface, P.q.twist t⟩)).subset ?_
  rintro c ⟨Q, rfl, α, ⟨f⟩⟩
  obtain ⟨t, ht, v, hv⟩ := hTα α
  exact ⟨t, ht, Quotient.sound ⟨(conjUnitIso P.q t α v hv).trans f⟩⟩

/-- **`π₆` is onto `P¹(ℚ̄)`** for any coarse witness and any `π₆` with the fibre clause of `R2X6Props`. -/
theorem surj_of_fibre {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY) (π₆ : ToP1 X.left)
    (hfib : ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (π₆.val (K := Qbar) x.left = π₆.val (K := Qbar) x'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q))) :
    ∀ t : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = t := by
  obtain ⟨hp, hs, hne, -, -, -⟩ := h6
  refine curveFacts.2 X hp hs hne π₆ fun x => ?_
  obtain ⟨P, hP⟩ := Quotient.exists_rep (Ψ x)
  refine ((pairTwistClass_finite P).preimage Ψ.injective.injOn).subset ?_
  intro x' hx'
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x')
  refine ⟨Q, hQ.symm, (hfib x x' P Q hP.symm hQ.symm).1 hx'.symm⟩

end ShimuraSplit

#print axioms ShimuraSplit.surj_of_fibre
