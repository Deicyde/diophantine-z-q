import ZInQKernel.Contrib.OneProof.RC.ModelTarget.BaseChangeIso
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.GroupObj
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ComplexReading

/-! The detector's good cubic, tex 8477–8479. For an integral Weierstrass equation `W₀`
with discriminant prime to the detector `ℓ ≥ 5`, the projective cubic `E` of its
localization at `ℓ` is smooth, a group object and a Néron model over the detector ring
(`WeierstrassSmooth`, `GroupObj`). Its generic fibre is the projective cubic of the fixed
rational equation `W₀⁄ℚ` and its special fibre is that of the reduction of `W₀` mod `ℓ`,
both by the identity in homogeneous coordinates (`bcIso`). On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve WeierstrassCurve.ModelTorsion
open scoped WeierstrassCurve

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

open GoodReduction (generic)

variable (ell : ℕ) [Fact ell.Prime] (W₀ : WeierstrassCurve ℤ)

/-- The localization of the good equation at the detector. -/
abbrev detW : WeierstrassCurve (LocalIntegers ell) := W₀.map (algebraMap ℤ (LocalIntegers ell))

theorem exists_detShear (h₅ : 5 ≤ ell) :
    ∃ c w : LocalIntegers ell,
      w * (c ^ 3 + (detW ell W₀).a₂ * c ^ 2 + (detW ell W₀).a₄ * c + (detW ell W₀).a₆) = -1 := by
  obtain ⟨c, hc⟩ := exists_shear ell Fact.out h₅ W₀.a₂ W₀.a₄ W₀.a₆
  let u : (integerPrimeIdeal ell).primeCompl :=
    ⟨c ^ 3 + W₀.a₂ * c ^ 2 + W₀.a₄ * c + W₀.a₆, by
      simpa [integerPrimeIdeal, Ideal.mem_span_singleton] using hc⟩
  obtain ⟨v, hv⟩ := (IsLocalization.map_units (LocalIntegers ell) u).exists_right_inv
  refine ⟨algebraMap ℤ _ c, -v, ?_⟩
  simp only [map_a₂, map_a₄, map_a₆]
  rw [neg_mul, mul_comm, ← neg_neg (1 : LocalIntegers ell)]
  congr 1
  rw [← hv]
  simp [u, map_add, map_mul, map_pow]

variable {ell W₀}

theorem smooth_mapped {S : Type} [CommRing S] (ψ : LocalIntegers ell →+* S) (h₅ : 5 ≤ ell)
    (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) : Smooth (projStructure ((detW ell W₀).map ψ)) := by
  have := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  obtain ⟨c, w, hw⟩ := exists_detShear ell W₀ h₅
  refine smooth_projStructure ((detW ell W₀).map ψ) (c := ψ c) (w := ψ w) ?_
  have := congrArg ψ hw
  simpa only [map_a₂, map_a₄, map_a₆, map_mul, map_add, map_pow, map_neg, map_one] using this

theorem reduced_mapped {S : Type} [Field S] (ψ : LocalIntegers ell →+* S) (h₅ : 5 ≤ ell)
    (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) : IsReduced (Proj ((detW ell W₀).map ψ).toProjective.grading) :=
  isReduced_of_smooth_hom (T := cubic ((detW ell W₀).map ψ)) (smooth_mapped ψ h₅ hΔ)

theorem reduced_baseChange {S : Type} [Field S] (ψ : LocalIntegers ell →+* S) (h₅ : 5 ≤ ell)
    (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) : IsReduced (baseChangeScheme (detW ell W₀) ψ) := by
  have hs : Smooth (cubic (detW ell W₀)).hom := weierstrassModel_smooth ell h₅ W₀ hΔ
  exact isReduced_of_smooth_hom
    (T := (Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj (cubic (detW ell W₀)))
    (by change Smooth (pullback.snd _ _); infer_instance)

/-- The detector's comparison of a fibre with the cubic of the mapped equation. -/
def detFibreIso {S : Type} [Field S] (ψ : LocalIntegers ell →+* S) (h₅ : 5 ≤ ell)
    (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj (cubic (detW ell W₀)) ≅
      cubic ((detW ell W₀).map ψ) :=
  haveI := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  haveI := reduced_mapped ψ h₅ hΔ
  haveI := reduced_baseChange ψ h₅ hΔ
  bcIso (detW ell W₀) ψ

theorem detW_map_eq {S : Type} [CommRing S] (ψ : LocalIntegers ell →+* S) (κ : ℤ →+* S) :
    (detW ell W₀).map ψ = W₀.map κ := by
  rw [detW, WeierstrassCurve.map_map]
  congr 1
  exact Subsingleton.elim _ _

/-- **The generic fibre of the good cubic is the projective cubic of the fixed rational
equation** `W₀⁄ℚ`, by the identity in homogeneous coordinates. -/
def detGenericIso (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    (generic (LocalIntegers ell) ℚ).obj (ModelNeron.weierstrassModel ell (detW ell W₀)) ≅
      PMWire.ellipticTarget (W₀⁄ℚ) :=
  detFibreIso (algebraMap (LocalIntegers ell) ℚ) h₅ hΔ ≪≫
    eqToIso (congrArg cubic (detW_map_eq (algebraMap (LocalIntegers ell) ℚ) (algebraMap ℤ ℚ)))

theorem detProperGeneric (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    IsProper ((generic (LocalIntegers ell) ℚ).obj (ModelNeron.weierstrassModel ell (detW ell W₀))).hom := by
  have := ModelNeron.weierstrassModel_proper ell (detW ell W₀)
  change IsProper (pullback.snd _ _)
  infer_instance

theorem detGeomIntGeneric (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    GeometricallyIntegral
      ((generic (LocalIntegers ell) ℚ).obj (ModelNeron.weierstrassModel ell (detW ell W₀))).hom := by
  have : (W₀⁄ℚ).IsElliptic := by
    have h := ModelNeron.isElliptic_at_detector ell W₀ hΔ
    rw [show W₀⁄ℚ = (detW ell W₀).map (algebraMap (LocalIntegers ell) ℚ) from
      (detW_map_eq (algebraMap (LocalIntegers ell) ℚ) (algebraMap ℤ ℚ)).symm]
    infer_instance
  let _ := complexLaw (W₀⁄ℚ)
  let A := J0Cusps.projectiveAbVar (W₀⁄ℚ)
  let jE := detGenericIso h₅ hΔ
  have hpb : IsPullback jE.hom.left
      ((generic (LocalIntegers ell) ℚ).obj (ModelNeron.weierstrassModel ell (detW ell W₀))).hom
      (J0Cusps.projectiveTarget (W₀⁄ℚ)).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w jE.hom).trans (Category.comp_id _).symm⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hpb (PkgI3.AbVar.geomInt A)

#print axioms exists_detShear
#print axioms smooth_mapped
#print axioms reduced_baseChange
#print axioms detFibreIso
#print axioms detGenericIso
#print axioms detProperGeneric
#print axioms detGeomIntGeneric

end ZInQ.Manuscript.RC.ModelTarget
