import ZInQKernel.HDecomp.ModCurves.X1Belyi

/-! # curves-g: the rational-point clause of `X1Belyi.CurveOfFunctionFieldQ` (T38)

A proper integral `ℚ`-scheme whose function field has a place of degree one over `ℚ` has a
`ℚ`-point (valuative criterion of properness, Mathlib `UniversallyClosed.eq_valuativeCriterion`,
Stacks 01KF). Hence `X1Belyi.CurveOfFunctionFieldQ` follows from its clause without the point,
`CurveOfFunctionFieldQNoPoint`. No `sorry`, no `axiom`. -/

noncomputable section

namespace ZInQ.Contrib.CurvesG

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory LeafModCurves X1Belyi

/-- Any two morphisms to `Spec ℚ` agree. -/
theorem hom_to_specQ_ext {S : Scheme} (f g : S ⟶ SpecQ) : f = g :=
  ext_to_Spec (CommRingCat.hom_ext (Subsingleton.elim _ _))

section residue

variable {F : Type} [Field F] (r : ℚ →+* F) (w : ValuationSubring F)
  (hw : ∀ c : ℚ, r c ∈ w)

/-- `ℚ → w`. -/
def ratToW : ℚ →+* w := r.codRestrict w.toSubring hw

/-- `ℚ → κ(w)`. -/
def ratToResidue : ℚ →+* IsLocalRing.ResidueField w :=
  (IsLocalRing.residue w).comp (ratToW r w hw)

theorem ratToResidue_bijective (hres : ∀ x ∈ w, ∃ c : ℚ, x - r c ∈ w.nonunits) :
    Function.Bijective (ratToResidue r w hw) := by
  refine ⟨(ratToResidue r w hw).injective, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hres x x.2
  refine ⟨c, ?_⟩
  show IsLocalRing.residue w (ratToW r w hw c) = IsLocalRing.residue w x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have h : x - ratToW r w hw c ∈ IsLocalRing.maximalIdeal w :=
    ValuationSubring.coe_mem_nonunits_iff.mp hc
  rw [← neg_sub]
  exact neg_mem h

/-- The residue map `w → κ(w) ≅ ℚ` of a place of degree one. -/
def residueToRat (hres : ∀ x ∈ w, ∃ c : ℚ, x - r c ∈ w.nonunits) : w →+* ℚ :=
  (RingEquiv.ofBijective _ (ratToResidue_bijective r w hw hres)).symm.toRingHom.comp
    (IsLocalRing.residue w)

end residue

/-- **Glue (proved).** Let `X` be a proper integral scheme over `ℚ`, `F` a field isomorphic to its
function field, and `w` a valuation subring of `F` containing `ℚ` with residue field `ℚ` (every
element of `w` is congruent to a rational modulo `𝔪_w`). Then `X` has a `ℚ`-point: the valuative
criterion lifts `Spec F → X` to `Spec w → X`, and the closed point `Spec ℚ = Spec κ(w) → Spec w`
gives the point. -/
theorem nonempty_ratPt_of_place (X : Over SpecQ) [IsProper X.hom] [IsIntegral X.left]
    {F : Type} [Field F] (e : X.left.functionField ≃+* F) (r : ℚ →+* F)
    (w : ValuationSubring F) (hw : ∀ c : ℚ, r c ∈ w)
    (hres : ∀ x ∈ w, ∃ c : ℚ, x - r c ∈ w.nonunits) : Nonempty (RatPt X) := by
  let i₁ : Spec (CommRingCat.of F) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.left.fromSpecStalk (genericPoint X.left)
  let i₂ : Spec (CommRingCat.of w) ⟶ SpecQ := Spec.map (CommRingCat.ofHom (ratToW r w hw))
  let S : ValuativeCommSq X.hom :=
    { R := w, K := F, i₁ := i₁, i₂ := i₂, commSq := ⟨hom_to_specQ_ext _ _⟩ }
  have hUC : UniversallyClosed X.hom := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hUC
  obtain ⟨l⟩ := (hUC.1 S).exists_lift
  let pt : SpecQ ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (residueToRat r w hw hres)) ≫ l.l
  exact ⟨Over.homMk pt (hom_to_specQ_ext _ _)⟩

/-- **T38 without the point clause** (published; the leaf `X1Belyi.CurveOfFunctionFieldQ` minus
its clause "`X` has a `ℚ`-point when `F` has a place of degree 1", which is proved here). Let `F`
be a finite extension of `ℚ(T)` in which `ℚ` is algebraically closed. Then there is a smooth
proper geometrically connected integral curve `X` over `ℚ` with function field `F`. Source:
the Stacks Project, *Algebraic Curves*, section "Curves and function fields" (Tag 0BXX,
UNVERIFIED tag: a finitely generated field extension of transcendence degree 1 is the function
field of a normal projective curve, unique up to isomorphism); normal of dimension 1 over a
perfect field implies smooth (Stacks 0B8X, UNVERIFIED); `H⁰(X, 𝒪_X)` is the algebraic closure of
`ℚ` in `F` and proper with `H⁰ = k` implies geometrically connected (Stacks 0BUG, UNVERIFIED);
Hartshorne I.6.7-6.12, II.6.7 over an algebraically closed field (UNVERIFIED numbers). -/
def CurveOfFunctionFieldQNoPoint : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F →
    ∃ X : Over SpecQ, IsCurve X ∧ ∃ (_ : IsIntegral X.left), Nonempty (X.left.functionField ≃+* F)

/-- **Reduction (proved): T38 from its point-free form.** -/
theorem curveOfFunctionFieldQ_of_noPoint (h : CurveOfFunctionFieldQNoPoint) :
    CurveOfFunctionFieldQ := by
  intro F _ _ _ hF
  obtain ⟨X, hX, hI, ⟨e⟩⟩ := h F hF
  refine ⟨X, hX, ?_, hI, ⟨e⟩⟩
  rintro ⟨w, -, hw, hres⟩
  have := hX.proper
  exact nonempty_ratPt_of_place X e (ratHom F) w hw hres

end ZInQ.Contrib.CurvesG
