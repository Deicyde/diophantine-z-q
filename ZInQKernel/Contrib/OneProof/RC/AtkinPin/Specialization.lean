import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Generic
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Geometry

/-! The exact pointwise specialization interface at tex 8476–8489.
Applying an additive reduction map to the based generic identity is
on-the-spot (c). -/

set_option autoImplicit false

noncomputable section

open scoped Classical TauCeti.ExactDivisor
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open FreeAbelianGroup (of)

namespace ZInQ.Manuscript.RC.AtkinPin

open PreparedParam
open PMGeometry (DivZero center)

variable {N Q : ℕ} [NeZero N] {E : WeierstrassCurve ℚ} [E.IsElliptic]
  {X : X0Model N} {hQ : Q ∥ N}
  (W : RationalAtkin X hQ) (π : X.X ⟶ Proj E.toProjective.grading)
  (hπ : π ≫ projectiveOverQ E = X.overQ) (b : FieldPoint X.overQ ℚ)

variable {ell : ℕ} [Fact ell.Prime] {K : Type} [Field K] [Algebra (ZMod ell) K]
  [DecidableEq K] {Ebar : WeierstrassCurve (ZMod ell)} {Y : PMAdelic.CoarseFibre}
  (infinity : Y.Point) {J : Type} [AddCommGroup J] (divisorClass : DivZero Y.Point →+ J)
  (quotient : J →+ PM.ReducedPoints (K := K) Ebar)

/-- For each coarse supersingular point, compare the reductions of the two
generic based differences with the two indicated coarse divisor classes.
The second comparison uses the images of both lifts under the same
rational Atkin–Lehner map. This is a condition about reduction; it
contains neither an eigenvalue nor an assertion about any CM lift. -/
def BasedSpecialization (p : ℕ) : Prop :=
  ∀ x ∈ Y.ss, ∃ (F : Type) (_ : Field F) (_ : Algebra ℚ F)
    (y : FieldPoint X.overQ F)
    (red : (E.baseChange F).toAffine.Point →+ PM.ReducedPoints (K := K) Ebar),
    let a := b.map (Algebra.ofId ℚ F)
    let P := fun t : FieldPoint X.overQ F => projectiveValue (t.comp π hπ).val
    red (P y - P a) = quotient (divisorClass (center infinity (of x))) ∧
      red (P (y.comp W.hom W.overQ) - P (a.comp W.hom W.overQ)) =
        quotient (divisorClass (center infinity (of (Y.W p x) - of (Y.W p infinity))))

set_option backward.isDefEq.respectTransparency false in
/-- Specialize the based generic identity to the field required by
`AtkinSign.SpecialFibreAtSigns.atkin_quotient` at a single prime. -/
theorem atkin_quotient_of_specialization (p : ℕ) (e : ℤ)
    (ha : BasedAtkinOnPoints X W π hπ b e)
    (hb : BasedSpecialization W π hπ b infinity divisorClass quotient p) :
    ∀ x ∈ Y.ss,
      quotient (divisorClass (center infinity (of (Y.W p x) - of (Y.W p infinity)))) =
        e • quotient (divisorClass (center infinity (of x))) := by
  intro x hx
  obtain ⟨F, _, _, y, red, hbase, hmove⟩ := hb x hx
  rw [← hmove, ha F y, map_zsmul, hbase]

/-- For a level prime the conclusion has exactly the sign of the theta
stage. There is no separate sign agreement hypothesis. -/
theorem pinned_atkin_quotient_of_specialization
    (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1)
    (p : ℕ)
    (V : RationalAtkin X (TauCeti.Nat.isExactDivisor_primePow (p := p)))
    (ha : BasedAtkinOnPoints X V π hπ b (wNew f hχ p : ℤ))
    (hb : BasedSpecialization V π hπ b infinity divisorClass quotient p) :
    ∀ x ∈ Y.ss,
      quotient (divisorClass (center infinity (of (Y.W p x) - of (Y.W p infinity)))) =
        (wNew f hχ p : ℤ) • quotient (divisorClass (center infinity (of x))) :=
  atkin_quotient_of_specialization V π hπ b infinity divisorClass quotient p _ ha hb


end ZInQ.Manuscript.RC.AtkinPin
